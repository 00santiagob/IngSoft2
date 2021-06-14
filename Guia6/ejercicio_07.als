/*
	Practico 6
	Ejercicio 7
*/

sig Interprete {}
sig Cancion {}
sig Catalogo {
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
}{
/*
Es consistente si todas las canciones del catalogo
estan registradas por algun interprete y todo interprete
del catalogo tiene registrada alguna cancion.
*/
	interpretaciones.interpretes = canciones
	~interpretaciones.canciones = interpretes
}

pred show[cat: Catalogo] {}
pred agregar_interpretacion[cat, cat': Catalogo, c: Cancion, i: Interprete] {
	cat != cat' // Es necesario
	cat'.interpretaciones = cat.interpretaciones + (c -> i)
}
pred eliminar_interpretacion[cat, cat': Catalogo, c: Cancion, i: Interprete] {
	cat != cat' // Es necesario
	cat'.interpretaciones = cat.interpretaciones - (c -> i)
}
pred quienes_interpretan[cat: Catalogo, i: Interprete -> Interprete] {
	i = ~(cat.interpretaciones).(cat.interpretaciones)
}

run show for  3 Cancion, 3 Interprete, 1 Catalogo
run agregar_interpretacion for 3 Cancion, 3 Interprete, exactly 2 Catalogo
run eliminar_interpretacion for 3 Cancion, 3 Interprete, exactly 2 Catalogo
run quienes_interpretan for 3 Cancion, 3 Interprete, 1 Catalogo

add_remove: check {
	all cat, cat': Catalogo |
		all c: cat.canciones |
			all i: c.(cat.interpretaciones) |
				eliminar_interpretacion[cat, cat', c, i] => agregar_interpretacion[cat', cat, c, i]

}
