module SistemaDePermissão

abstract sig User{
		leitura: set Object,
		escrita: set Object,
		dono : set Object
}
one sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}

abstract sig Object {}
one sig Root extends Object{
	filho : set Object
}
some sig Dir extends Object{
	filho : set Object
}
some sig File extends Object{}


fact{
	all u: User| #(u.leitura& u.escrita) = 0 && #(u.leitura& u.dono) = 0 && #(u.dono& u.escrita) = 0 && #(u.leitura& u.escrita& u.dono) =0
	all u: User| u.leitura + u.escrita + u.dono = Object
	all r: Root , d: Dir| !(r in d.filho) && !(d in d.filho)
	all r:Root, d:Dir| d in r.filho ||some d2:Dir| d in d2.filho
	all f:File, d:Dir, r:Root | f in r.filho || f in d.filho
	--all u:User, o:Object| 
}
pred show[]{}
run show for 17
