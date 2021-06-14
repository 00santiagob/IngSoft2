/*
	Practico 6
	Ejercicio 10

	Torres de Hanoi
*/

open util/ordering[Torres]

abstract sig Discos {}

one sig D1, D2, D3, D4, D5, D6, D7 extends Discos {
	orden: D1 -> (Discos - D1) +
		   D2 -> (Discos - D1 - D2) +
		   D3 -> (Discos - D1 - D2 - D3) +
		   D4 -> (Discos - D1 - D2 - D3 - D4) +
		   D5 -> (Discos - D1 - D2 - D3 - D4 - D5) +
		   D6 -> (Discos - D1 - D2 - D3 - D4 - D5 - D6)
}

sig Torres {
	izq: set Discos,
	cen: set Discos,
	der: set Discos
}

fact inicial {
	first[].izq = Discos and no first[].cen and no first[].der
}

pred mover_disco[t, t': Torres, d: Discos] {
	(some d: t.izq |
		t'.izq = t.izq - d &&
			((t'.cen = t.cen + d && t'.der = t.der) ||
			 (t'.cen = t.cen && t'.der = t.der + d))
	) || (
	some d: t.cen |
		t'.cen = t.cen - d &&
			((t'.izq = t.izq + d && t'.der = t.der) ||
			 (t'.izq = t.izq && t'.der = t.der + d))
	) || (
	some d: t.der |
		t'.der = t.der - d &&
			((t'.izq = t.izq + d && t'.cen = t.cen) ||
			 (t'.izq = t.izq && t'.cen = t.cen + d))
	)
}

fact Transicion {
	all t: Torres, t': next[t] |
		some d: Discos |
			( d in t.izq => mover_disco[t, t'] ) &&
			( d in t.cen => mover_disco[t, t'] ) &&
			( d in t.der => mover_disco[t, t'] )
}
