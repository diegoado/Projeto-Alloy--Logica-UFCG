module SistemaDePermissão
open util/ordering[Time]

sig Time{}

abstract sig User{
		leitura: Object -> Time,
		escrita: Object -> Time,
		dono : Object -> Time
}
one sig ParaTodos, UsuariosExternos, UsuariosDesteComputador extends User{}



abstract sig Object {}

one sig Root extends Dir{}

sig Dir extends Object{
	filho : Object -> Time
}

sig File extends Object{}

pred init[t: Time] {
	all u: User | (u.leitura).t + (u.escrita).t + (u.dono).t = Root
	all d: Dir | no d.filho.t
	
}

fact{
	all u: User, t: Time | no((u.leitura).t &  (u.escrita).t) && no((u.leitura).t &  (u.dono).t) && no((u.dono).t &  (u.escrita).t)
	all u: User, t: Time | (u.leitura).t + (u.escrita).t + (u.dono).t = Root.^(filho.t) + Root
	all d: Dir, t: Time | Root !in d.filho.t
	all d: Dir, t: Time | (d !in Root.^(filho.t) => no d.filho
	no d: Dir, t: Time | d in d.^(filho.t)
	all o: Object, t: Time | lone d: Dir | o in (d.filho).t

	all o: Object, u: User, t: Time | (o in (u.leitura).t) => (o.^(filho.t) in (u.leitura).t)
	all o: Object, u: User, t: Time | (o in (u.escrita).t) => (all filhos: o.^(filho.t) | filhos !in (u.dono).t)
}

pred addObject[o:Object,d:Dir,ti,tf: Time]{
	o !in Root.^(filho.ti)
	Root.^(filho.tf) = Root.^(filho.ti) + o
	(d.filho).tf = (d.filho).ti + o
}

fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		one d: (Root + Root.^(filho.pre)), o: Object | addObject[o,d,pre,pos]

	
}

pred show[]{}
run show for 7
