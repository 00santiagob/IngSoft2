/*
	Practico 6
	Ejercicio 5 - a
*/
// Elementos
sig Elem {}
// Relacion entre Elementos
sig Rel {
	rel: Elem -> Elem
}

// Axiomas basicos
pred reflexiva[r:Rel] {
	(iden & (Elem -> Elem)) in r.rel
}
pred simetrica[r:Rel] { // PARATODO x,y : xRy ==> yRx
	r.rel = ~(r.rel)
}
pred antisimetrica[r:Rel] { // PARATODO x,y : xRy ^ yRx ==> x=y
	(r.rel & ~(r.rel)) in iden
}
pred transitiva[r:Rel] { // PARATODO x,y : xRy ^ yRz ==> xRz
	(r.rel).(r.rel) in r.rel
}
// Muestra los axiomas
pred show[r:Rel] {
	reflexiva[r]
	simetrica[r]
	//antisimetrica[r]
	//transitiva[r]
	//preorden[r]
	//some r.rel
}

// Ejercicio 5 - a)
pred preorden[r:Rel] { // reflexiva y transitiva, puede tener ciclos
	reflexiva[r]
	transitiva[r]
	not antisimetrica[r]
}

run show for exactly 3 Elem, 1 Rel

