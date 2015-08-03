module SistemaDePermissão
open util/ordering[Time]

sig Time{}

abstract sig User{
		leitura: set Object -> Time,
		escrita: set Object -> Time,
		dono : set Object -> Time
}
one sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}

abstract sig Object {}

one sig Root extends Dir{}

sig Dir extends Object{
	filho : set Object -> Time
}

sig File extends Object{}

pred init[t: Time] {
	one Object
}

fact{
	all u: User, t: Time | no(t.~(u.leitura) &  t.~(u.escrita)) && no(t.~(u.leitura) &  t.~(u.dono)) && no(t.~(u.dono) &  t.~(u.escrita))
	all u: User, t: Time | t.~(u.leitura) + t.~(u.escrita) + t.~(u.dono) = Object
	all o: Object, t: Time | (o != Root) => (o in Root.^(filho.t))
	no d: Dir, t: Time | d in d.^(filho.t)
	all o: Object, t: Time | (o != Root) => one d: Dir | o in t.~(d.filho)

	all o: Object, u: User | (o in u.leitura) => (all filhos: o.^filho | filhos in u.leitura)
	all o: Object, u: User | (o in u.escrita) => (all filhos: o.^filho | filhos !in u.dono)
}

pred addObject[o:Object,d:Dir,t,t': Time]{
	o !in (d.filho).t
	(d.filho).t' = (d.filho).t + o
}

fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some d: Dir, o: Object | addObject[o,d,pre,pos]
}

pred show[]{}
run show for 4
