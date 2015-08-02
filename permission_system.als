module SistemaDePermissão

abstract sig User{
		leitura: set Object,
		escrita: set Object,
		dono : set Object
}
one sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}

abstract sig Object {}

some sig File extends Object{} 
one sig Root extends Dir{}
some sig Dir extends Object{
	filho : set Object
}

fact{
	all u: User| no(u.leitura &  u.escrita) && no(u.leitura &  u.dono) && no(u.dono &  u.escrita)
	all u: User| u.leitura + u.escrita + u.dono = Object
	all o: Object | (o != Root) => (o in Root.^filho)
	no d: Dir | d in d.^filho
	all o: Object | (o != Root) => one d: Dir | o in d.filho
	all o: Object, u: User | (o in u.leitura) => (all filhos: o.^filho | filhos in u.leitura)
	all o: Object, u: User | (o in u.escrita) => (all filhos: o.^filho | filhos !in u.dono)
}

pred show[]{}
run show for 5
