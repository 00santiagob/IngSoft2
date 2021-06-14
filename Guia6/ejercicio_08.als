/*
	Practico 6
	Ejercicio 8

    Link: http://beeks.eu/Puzzle3.htm
    Variante del problema de Cruzar el Rio pero con mas personajes.
*/

open util/ordering[Estado]

abstract sig Elemento {}

one sig Balsa extends Elemento {}

abstract sig Persona extends Elemento {
	kills: set Persona,
	controls: set Persona
}

one sig Policia, Preso, Mujer, Hombre, Nene1, Nene2, Nena1, Nena2 extends Persona {}

fact killing {
		kills = Preso -> (Persona - Policia - Preso) +
				Mujer -> Nene1 +
				Mujer -> Nene2 +
				Hombre -> Nena1 +
				Hombre -> Nena2
}

fact controlling {
	controls = Policia -> Preso +
			  Mujer -> Hombre +
			  Hombre -> Mujer
}

sig Estado {
	izq: set Elemento,
	der: set Elemento
}

fact estado_inicial {
	first[].izq = Elemento and no first[].der
}

fun conflict[x: set Elemento]: set Elemento {
	x - (x - x.controls).kills
}

pred cruzar_rio [aca, aca', alla, alla': set Elemento] {
    some responsable: conflict[aca] & (Policia + Hombre + Mujer) |
    	(aca' = conflict[aca] - responsable - Balsa &&
    	alla' = conflict[alla] + responsable + Balsa
    	) || (
    	some persona: conflict[aca] - responsable - Balsa |
    		aca' = conflict[aca] - responsable - persona - Balsa &&
    		alla' = alla - conflict[alla]  + Balsa +
    				(responsable - persona.kills) +
					(persona - responsable.kills)
    	)
}

fact Transicion_de_estados {
	all e: Estado, e': next[e] |
		(Balsa in e.izq  => cruzar_rio[e.izq, e'.izq, e.der, e'.der]) &&
		(Balsa in e.der => cruzar_rio[e.der, e'.der, e.izq, e'.izq])
}

pred solvePuzzle[] {
	some e:Estado | e.der = Elemento
}

run solvePuzzle for 19
