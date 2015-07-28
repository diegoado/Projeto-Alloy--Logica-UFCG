module PermissionSystem

-- Restringir que não pode haver permissão sem diretório

--sig User{}
--sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}

sig Permissao{}
sig Leitura, LeituraEscrita, Dono extends Permissao{}


sig Dir{
	parent: lone Dir,
	premissao : one Permissao,
	--usuario : one User
}

one sig Root extends Dir {}

fact {
	all d: Dir | d !in d.^parent
	all d: Dir | (d != Root) => (Root in d.^parent)
	no Root.parent
	Permissao = Leitura + LeituraEscrita + Dono
	--User = ParaTodos + UsuariosExternos + UsuariosDesteComputador
}

sig File{
	dir: one Dir
}

pred show[]{}
run show for 3
