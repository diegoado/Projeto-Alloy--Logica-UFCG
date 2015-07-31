module PermissionSystem

abstract sig User{
	permissoes: Object -> one Permissao
}
one sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}
 
abstract sig Permissao{
	obj: set Object 
}
one sig Leitura, LeituraEscrita, Dono extends Permissao{}
 
abstract sig Object {
	parent: lone Dir,
--	usuario: one User
}
 
sig Dir, File extends Object{}

one sig Root extends Dir {}
 
fact {
		all o: Object | (o != Root) => #(o.parent) = 1
        no Root.parent
        all d: Dir | d !in d.^parent
        all d: Dir | (d != Root) => (Root in d.^parent)
		all u: User, o: Object | (o.(u.permissoes) = LeituraEscrita) => ( Leitura !in (o.^parent).(u.permissoes))
		all u: User, o: Object | (o.(u.permissoes) = Dono) => (all permissao: (o.^parent).(u.permissoes) | permissao = Dono)
}

assert teste{
	all u: User, o: Object | #(o.(u.permissoes)) = 1
}

--check teste
 
pred show[]{}
run show for 5
