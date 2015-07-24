module SistemaDePermissao

sig Dir{
	parent: lone Dir
}

one sig Root extends Dir {}

fact {
	all d: Dir | d !in d.^parent
	all d: Dir | (d != Root) => (Root in d.^parent)
	no Root.parent
}

sig File{
	dir: one Dir
}

pred show[]{}
run show for 3
