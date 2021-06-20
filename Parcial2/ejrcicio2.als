/*
	Parcial 2 - Ingenieria del Software 2
	Santiago A. Balog
	Ejercicio 2
*/

/*  Las partes de codigo que estan comentadas no son requeridas para el parcial, pero me parecieron correctos para un mejor analisis  */

sig VueloID, Ciudad, Horario {}
sig Alianza {}
sig Aerolinea {
	vID: set VueloID,
	desde: set Ciudad,
	hasta: set Ciudad,
	horaPartida: set Horario,
	horaArribo: set Horario,
	ruta: vID -> one (desde -> hasta), // a) cada vuelo tiene una unica ruta directa asociada
	partidas: vID -> one horaPartida, // a) cada vuelo tiene un unico horario de partida
	arribos: vID -> one horaArribo, // a) cada vuelo tiene un unico horario de llegada
	socio: lone Alianza // c) una aerolinea puede ser socia a lo sumo de una alianza
}{
	// b) ninguna aerolinea puede tener parcialmente definidos los vuelos,
	vID in ruta.hasta.desde
	vID in partidas.horaPartida
	vID in arribos.horaArribo

	/*
	// Por gusto propio tambien me intereza que los horarios esten definidos de forma total
	horaPartida in vID.partidas
	horaArribo in vID.arribos
	// Y que las ciudades esten definidas de forma total
	desde in (vID.ruta).hasta
	hasta in desde.(vID.ruta)
	*/
}

// d) los numeros de vuelo son globalmente unicos, es decir, dos aerolineas distintas no pueden tener el mismo numero de vuelo.
fact VuelosID_Unicos {
	all aero_1, aero_2: Aerolinea | (aero_1 != aero_2)
		=> not some vID1, vID2: VueloID |
			(vID1 in aero_1.vID and vID2 in aero_2.vID and vID1 = vID2)
}

/*
// Me parece mejor que los horarios de partida y arribo de un mismo vuelo sean distintos 
fact partida_arribo_distintos {
	all a: Aerolinea | all v: (a.vID) |
		v.(a.partidas) != v.(a.arribos)
}

// Dos o mas vuelos de la misma Aerolinea con la misma ruta directa, no deben tener mismo horas de partida y arribo
fact misma_ruta_distinto_horario {
	all a: Aerolinea | some vID1, vID2: (a.vID) |
		(vID1.(a.ruta) = vID2.(a.ruta)) => ((vID1.(a.partidas) != vID2.(a.partidas)) and (vID1.(a.arribos) != vID2.(a.arribos)))
}
*/

// e) Determina si hay alguna ruta posible entre dos ciudades con la misma aerolinea
pred chequeo_de_ruta [ a: Aerolinea, d, h: Ciudad ] {
	(d -> h) in ^((a.vID).(a.ruta))
}

// f) Retorna los vuelos posibles para una ruta directa a un horario especifico, todos pertenecientes a la misma alianza
fun vuelo_directo [ alianza: Alianza, d, h: Ciudad, hsP: Horario ] : (set VueloID) {
	{
		vuelos: (Aerolinea.partidas.hsP) & (Aerolinea.ruta.d.h) |
			all a: Aerolinea | (a.socio = Alianza) and (a.vID = vuelos)
	}
}

run chequeo_de_ruta for 5
run {} for 3 but exactly 1 Alianza
