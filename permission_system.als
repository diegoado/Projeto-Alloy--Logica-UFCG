module SistemaDePermissão

abstract sig User{
		leitura: set Object,
		escrita: set Object,
		dono : set Object
}
one sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}

abstract sig Object{}

sig File extends Object{} 
one sig Root extends Dir{}
sig Dir extends Object{
	filho : set Object
}

fact{
	all u: User| no(u.leitura &  u.escrita) && no(u.leitura &  u.dono) && no(u.dono &  u.escrita)
	all u: User, r:Root| u.leitura + u.escrita + u.dono = r+ r.^filho
--	all d: Dir, r :Root| (d !in r.^filho)=> no d.filho -- ??
	no d: Dir | d in d.^filho
	all o: Object, r: Root | (o in r.^filho) => one d: Dir | o in d.filho
	all o: Object, u: User | (o in u.leitura) => (o.^filho in u.leitura)
	all o: Object, u: User | (o in u.escrita) => (all filhos: o.^filho | filhos !in u.dono)
}

assert teste{
 	all u: User, o: Object | o in (u.leitura + u.escrita + u.dono)
	all u: User, o: Object | (o in u.leitura) => (o.^filho in u.leitura)
	all u: User, o: Object | (o in u.escrita) => (all filhos: o.^filho | filhos !in u.dono)
	all r: Root, o: Object  | (o != Root) => (o in r.^filho)
}

check teste
pred show[]{}
run show for 5
