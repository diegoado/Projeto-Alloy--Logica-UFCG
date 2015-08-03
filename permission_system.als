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
	all u: User | (u.leitura).t + (u.escrita).t + (u.dono).t = Root
}

fact{
	all u: User, t: Time | no((u.leitura).t &  (u.escrita).t) && no((u.leitura).t &  (u.dono).t) && no((u.dono).t &  (u.escrita).t)
	all u: User, t: Time | (u.leitura).t + (u.escrita).t + (u.dono).t = Object
	all o: Object, t: Time | (o != Root) => (o in Root.^(filho.t))
	no d: Dir, t: Time | d in d.^(filho.t)
	all o: Object, t: Time | (o != Root) => one d: Dir | o in (d.filho).t

	all o: Object, u: User, t: Time | (o in (u.leitura).t) => (o.^(filho.t) in (u.leitura).t)
	all o: Object, u: User, t: Time | (o in (u.escrita).t) => (all filhos: o.^(filho.t) | filhos !in (u.dono).t)
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
run show for 5
