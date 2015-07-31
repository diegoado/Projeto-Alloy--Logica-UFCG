module PermissionSystem

sig Name {}

abstract sig User {
	read: lone Read,
	write: lone Write,
	owner: lone Owner,
	name: one Name
}
one sig ForAll, ExtUser, IntUser extends User{}
 
abstract sig Permission {
	object: some Object,
}
sig Read, Write, Owner extends Permission {}

abstract sig Object {
	parent: lone Dir,
}
 
sig File extends Object {}

sig Dir extends Object {
	file: set File
}

one sig Root extends Dir {}
 
fact {
		no Root.parent
        all d: Dir | d !in d.^parent
		all o: Object | (o != Root) => #(o.parent) = 1
        all d: Dir | (d != Root) => (Root in d.^parent)
		all u1: User, u2: User | u1 != u2 <=> u1.name != u2.name
		
		all o: Object | #(o.~object) = 3
		all p: Permission | one (p.~read + p.~write + p.~owner)
  		all o: Object | (o.~object = Write) => (all p: (o.^parent).~object | p != Read)
  		all o: Object | (o.~object = Owner) => (all p: (o.^parent).~object | p = Owner)
		all u: User | (no (u.read).object & (u.write).object) and (no (u.read).object & (u.owner).object) and (no (u.write).object & (u.owner).object)
}

assert teste{
--	all u: User, o: Object | #(o.(u.permissions)) = 1
}

pred show[]{}
run show for 5
