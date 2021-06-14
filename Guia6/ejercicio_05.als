/*
	Practico 6
	Ejercicio 5
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
pred irreflexiva[r:Rel] {
	no (iden & (Elem -> Elem) & r.rel)
}
pred simetrica[r:Rel] { // PARATODO x,y : xRy ==> yRx
	r.rel = ~(r.rel)
}
pred asimetrica[r:Rel] {
	no (r.rel & ~(r.rel))
}
pred antisimetrica[r:Rel] { // PARATODO x,y : xRy ^ yRx ==> x=y
	(r.rel & ~(r.rel)) in (iden & (Elem -> Elem))
}
pred transitiva[r:Rel] { // PARATODO x,y : xRy ^ yRz ==> xRz
	(r.rel).(r.rel) in r.rel
}
pred total[r:Rel] { // PARATODO x,y : xRy o yRx
	(Elem -> Elem) = (r.rel) + ~(r.rel) 
}

// Muestra los axiomas
pred show[r:Rel] {
// Descomentar el axioma que se quiere ver
	//reflexiva[r]
	//irreflexiva
	//simetrica[r]
	//asimetrica[r]
	//antisimetrica[r]
	//transitiva[r]
	//total
	some r.rel
}

// Ejercicio 5 - a) RELACION DE PRE-ORDEN
pred pre_orden[r:Rel] { // reflexiva y transitiva, puede tener ciclos
	reflexiva[r]
	transitiva[r]
	not antisimetrica[r]
	some r.rel
}

// Ejercicio 5 - b) RELACION DE ORDEN PARCIAL NO ESTRICTO (O REFLEXIVO)
pred orden_parcial[r:Rel] { // reflexiva, transitiva y antisimetrica
	reflexiva[r]
	transitiva[r]
	antisimetrica[r]
	some r.rel
}

// Ejercicio 5 - c) RELACION DE ORDEN TOTAL
pred orden_total[r:Rel] { // reflexiva, transitiva, antisimetrica y total
	reflexiva[r]
	transitiva[r]
	antisimetrica[r]
	total[r]
	some r.rel
}

// Ejercicio 5 - d) RELACION DE ORDEN PARCIAL ESTICTO (O IRREFLEXIBLE)
pred orden_estricto[r:Rel] { //irreflexiva, transitiva y asimetrica
	irreflexiva[r]
	transitiva[r]
	asimetrica[r]
	some r.rel
}

// Ejercicio 5 - e) RELACION QUE TIENE PRIMER ELEMENTO
pred primer_elemento[r:Rel] { // 
	reflexiva[r]
	transitiva[r]
	
}

// Ejercicio 5 - f) RELACION QUE TIENE ULTIMO ELEMENTO
pred ultimo_elemento[r:Rel] { // 
	
}

run show for exactly 5 Elem, 1 Rel
run pre_orden for 5 Elem, 1 Rel
run orden_parcial for 5 Elem, 1 Rel
run orden_total for 5 Elem, 1 Rel
run orden_estricto for exactly 5 Elem, 1 Rel
run primer_elemento for 5 Elem, 1 Rel
run ultimo_elemento for 5 Elem, 1 Rel

// Todo orden parcial es total
Parcial_es_Total: check {
	all r:Rel | orden_parcial[r] => orden_total[r]
} for 5 Elem, 1 Rel

// Todo orden parcial tiene primer elemento
Parcial_tiene_PrimerElem: check {
	all r:Rel | primer_elemento[r] in orden_parcial[r]
} for 5 Elem, 1 Rel

// Todo orden total con primer elemento 'x' y ultimo elemento 'y' satisface (x != y)
Total_PrimerElem_UltimoElem_distintos: check {} for 5 Elem, 1 Rel

// La union de ordenes estrictos es un orden estricto
Union_de_Estrictos: check {} for 5 Elem, 1 Rel

// La composicion de ordenes estrictos es un orden estricto
Composicion_de_Estrictos: check {} for 5 Elem, 1 Rel
