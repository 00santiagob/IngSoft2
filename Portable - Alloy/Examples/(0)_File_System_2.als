/*
	Tutorial: MIT - Alloy (2)
*/

// Un objeto del sistema de archivos en el sistema de archivos 
abstract sig FSObject {}

// Los objetos del sistema de archivos deben ser directorios o archivos
sig File, Dir extends FSObject {}

// Un sistema de archivos 
sig FileSystem {
	root: Dir,
	live: set FSObject,
	contents: Dir lone -> FSObject,
	// padre es el inverso del contenido
	parent: FSObject -> lone Dir
}{
	// root no tiene padre
	no root.parent
	// los objetos en vivo son accesibles desde la raiz
	live = root.*contents
	// contenido solo definido en objetos vivos
	contents in live -> live
	// padre es el inverso del contenido
	parent = ~contents
}

pred example {
	all fs : FileSystem | #fs.live > 2
}

run example for exactly 1 FileSystem, 4 FSObject
