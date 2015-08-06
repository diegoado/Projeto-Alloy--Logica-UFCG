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
sig File extends Object{}
sig Dir extends Object{
	filho : Object -> Time
}
one sig Root extends Dir{}

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
	User.leitura.tf - o = User.leitura.ti
	User.escrita.tf - o = User.escrita.ti
	User.dono.tf - o = User.dono.ti
	(d.filho).tf = (d.filho).ti + o
	all u2: User | u2.leitura.ti = u2.leitura.tf - o && u2.escrita.ti = u2.escrita.tf - o && u2.dono.ti = u2.dono.tf - o
	all d2: Dir - d | d2.filho.tf = d2.filho.ti
}

pred switchPermission[o:Object, u:User, ti,tf:Time]{
	o in u.(leitura + escrita).tf
	u.leitura.ti = u.leitura.tf - (o + o.^(filho.ti))
	u.escrita.ti = u.escrita.tf - (o + o.^(filho.ti))
	all u2: User - u | u2.leitura.tf = u2.leitura.ti && u2.escrita.tf = u2.escrita.ti && u2.dono.tf = u2.dono.ti
	all d: Dir | d.filho.tf = d.filho.ti
}

pred removeObject[o:Object, u: User, ti,tf:Time]{
	o in u.dono.ti
	o in	Root.^(filho.ti)
	o !in Root.^(filho.tf)
	Root.^(filho.tf) = Root.^(filho.ti) - (o + o.^(filho.ti))
	all u2: User  | u2.leitura.tf = u2.leitura.ti - (o + o.^(filho.ti)) && u2.escrita.tf = u2.escrita.ti - (o + o.^(filho.ti)) && u2.dono.tf = u2.dono.ti - (o + o.^(filho.ti))
	all d: Dir | d.filho.tf = d.filho.ti - (o + o.^(filho.ti))
}

pred init[t :Time]{
	no Root.filho.t
}

fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some d: (Root + Root.^(filho.pre)), o: Object | addObject[o,d,pre,pos] or
		some u: User, o:( u.dono.pre )| switchPermission[o,u,pre,pos] or
		some o: (Root + Root.^(filho.pre)), u: User| removeObject[o,u,pre,pos]
}

assert teste{
	all u: User, o: Object, t: Time | (o !in Root.^(filho.t) && o != Root)=> o !in (u.leitura + u.escrita + u.dono).t
	all u: User, o: Object, t: Time | (o in u.leitura.t) => (o.^(filho.t) in u.leitura.t)
	all u: User, o: Object, t: Time | (o in u.escrita.t) => (all filhos: o.^(filho.t) | filhos !in u.dono.t)
	all u: User, o: Object, t: Time | (o in u.dono.t) =>  o !in (u.leitura + u.escrita).t
}

check teste
pred show[]{}
run show for 5 but 15 Time
