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

pred init[t: Time] {}

fact{
	all u: User| no(u.leitura &  u.escrita) && no(u.leitura &  u.dono) && no(u.dono &  u.escrita)
	all u: User, t: Time | (u.leitura + u.escrita + u.dono).t = Root + Root.^(filho.t)
	all d: Dir, t: Time | Root !in d.filho.t
	no d: Dir, t: Time | d in d.^(filho.t)
	all d: Dir, t: Time | (d != Root &&d !in Root.^(filho.t)) => no d.filho.t
	all o: Object, t: Time | lone d: Dir | o in (d.filho).t
	all o: Object, u: User, t: Time | (o in (u.leitura).t) => (o.^(filho.t) in u.leitura.t)
	all o: Object, u: User, t: Time | (o in (u.escrita).t) => (all filhos: o.^(filho.t) | filhos !in u.dono.t)
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

assert teste{
	all u: User, o: Object, t: Time | (o !in Root.^(filho.t) && o != Root)=> o !in (u.leitura + u.escrita + u.dono).t
	all u: User, o: Object, t: Time | (o in u.leitura.t) => (o.^(filho.t) in u.leitura.t)
	all u: User, o: Object, t: Time | (o in u.escrita.t) => (all filhos: o.^(filho.t) | filhos !in u.dono.t)
	all u: User, o: Object, t: Time | (o in u.dono.t) =>  o !in (u.leitura + u.escrita).t
}

check teste

pred show[]{}
run show for 7
