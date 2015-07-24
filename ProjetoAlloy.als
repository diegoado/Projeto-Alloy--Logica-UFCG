module PermissionSytem

sig Dir {
	parent: lone Dir,
	files: set File
}
{
	this !in this.^@parent
	this != Root => Root in this.^@parent
}

sig File {
}

one sig Root extends Dir{}{ no this.@parent}

pred show[]{}
run show for 3
