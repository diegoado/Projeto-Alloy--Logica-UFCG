module PermissionSystem

abstract sig User{
	leitura: lone Leitura,
	leituraescrita: lone LeituraEscrita,
	dono: lone Dono
}
one sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}
 
abstract sig Permissao{
	obj: set Object
}
sig Leitura, LeituraEscrita, Dono extends Permissao{}
 
abstract sig Object {
	parent: lone Dir,
}
 
sig Dir, File extends Object{}

one sig Root extends Dir {}
 
fact {
		all u: User | (no (u.leitura).obj & (u.leituraescrita).obj) and (no (u.leitura).obj & (u.dono).obj) and (no (u.leituraescrita).obj & (u.dono).obj)
		all p: Permissao | one (p.~leitura + p.~leituraescrita + p.~dono)
		all o: Object | (o.~obj = LeituraEscrita) => (all p: (o.^parent).~obj | p != Leitura)
		all o: Object | (o.~obj = Dono) => (all p: (o.^parent).~obj | p = Dono)

		all o: Object | (o != Root) => #(o.parent) = 1
		all o: Object | #(o.~obj) = 3
        no Root.parent
        all d: Dir | d !in d.^parent
        all d: Dir | (d != Root) => (Root in d.^parent)
		--all u: User, o: Object | (o.(u.permissoes) = LeituraEscrita) => ( Leitura !in (o.^parent).(u.permissoes))
		--all u: User, o: Object | (o.(u.permissoes) = Dono) => (all permissao: (o.^parent).(u.permissoes) | permissao = Dono)
}

assert teste{
--	all u: User, o: Object | #(o.(u.permissoes)) = 1
}

--check teste
 
pred show[]{}
run show for 5
