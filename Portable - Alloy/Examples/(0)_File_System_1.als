/*
	Tutorial: MIT - Alloy (1)
*/

// Un objeto del sistema de archivos en el sistema de archivos 
sig FSObject { parent: lone Dir }

// Un directorio en el sistema de archivos 
sig Dir extends FSObject { contents: set FSObject }

// Un archivo en el sistema de archivos 
sig File extends FSObject { }

// Un directorio es el padre de su contenido 
fact { all d: Dir, o: d.contents | o.parent = d }

// Todos los objetos del sistema de archivos son archivos o directorios 
fact { File + Dir = FSObject }

// Existe una raíz 
sig Root extends Dir { } { no parent }

// El sistema de archivos está conectado 
fact { FSObject in Root.*contents }

// La ruta del contenido es acíclica 
assert acyclic { no d: Dir | d in d.^contents }

// Ahora compruébalo para un alcance de 5 
check acyclic for 5

// El sistema de archivos tiene una 
assert oneRoot { one d: Dir | no d.parent }

// Ahora verifíquelo para un alcance de 5
check oneRoot for 5

// Cada objeto fs está en como máximo un directorio 
assert oneLocation {
	all o: FSObject | lone d: Dir | o in d.contents
}

// Ahora verifíquelo para un alcance de 5
check oneLocation for 5
