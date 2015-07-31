module PermissionSystem

sig Name {}

abstract sig User{
	permissions: Object -> one Permission
	name: Name
}
one sig ForAll, ExtUser, IntUser extends User{}
 
abstract sig Permission{
	object: some Object 
}
one sig Read, Write, Owner extends Permission {}

abstract sig Object {
	parent: lone Dir,
	name: one Name
}
 
sig Dir, File extends Object {}

one sig Root extends Dir {}
 
fact {
		all o: Object | (o != Root) => #(o.parent) = 1
        no Root.parent
        all d: Dir | d !in d.^parent
        all d: Dir | (d != Root) => (Root in d.^parent)
		all u: User, o: Object | (o.(u.permissions) = Write) => ( Read !in (o.^parent).(u.permissions))
		all u: User, o: Object | (o.(u.permissions) = Owner) => (all permission: (o.^parent).(u.permissions) | permission = Owner)
}

assert teste{
	all u: User, o: Object | #(o.(u.permissions)) = 1
}

pred show[]{}
run show for 5
