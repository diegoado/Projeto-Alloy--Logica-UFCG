module PermissionSystem

-- Restringir que não pode haver permissão sem diretório

--sig User{}
--sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}

abstract sig Permissao{}
one sig Leitura, LeituraEscrita, Dono extends Permissao{}


sig Dir{
	parent: lone Dir,
	permissao : one Permissao,
	--usuario : one User
}

one sig Root extends Dir {}

fact {
	all d: Dir | d !in d.^parent
	all d: Dir | (d != Root) => (Root in d.^parent)
	no Root.parent
	all d: Dir | (d.permissao = LeituraEscrita) => ((d.^parent).permissao != Leitura)
	all d: Dir | (d.permissao = Dono) => ((d.^parent).permissao = Dono)
	--User = ParaTodos + UsuariosExternos + UsuariosDesteComputador
}

sig File{
	dir: one Dir
}


pred show[]{}
run show for 4
