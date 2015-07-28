module PermissionSystem

sig User{}

sig Permissao{}
sig Leitura in Permissao{}
sig LeituraEscrita in Permissao{}
sig Dono in Permissao{}

sig Dir{
	parent: lone Dir,
	premissao : one Permissao
}

one sig Root extends Dir {}

fact {
	all d: Dir | d !in d.^parent
	all d: Dir | (d != Root) => (Root in d.^parent)
	no Root.parent
	Permissao = Leitura + LeituraEscrita + Dono
}

sig File{
	dir: one Dir
}

pred show[]{}
run show for 3
