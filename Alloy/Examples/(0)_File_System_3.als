/*
	Tutorial: MIT - Alloy (3)
*/

// Un objeto del sistema de archivos en el sistema de archivos 
abstract sig FSObject {}

// Los objetos del sistema de archivos deben ser directorios o archivos
sig File, Dir extends FSObject {}

// Un sistema de archivos 
sig FileSystem {
	live: set FSObject,
	root: Dir & live,
	contents: Dir -> FSObject,
	// padre es el inverso del contenido
	parent: (live - root) -> one (Dir & live)
}{
	// los objetos en vivo son accesibles desde la raiz
	live = root.*contents
	// padre es el inverso del contenido
	parent = ~contents
}

pred example {
	all fs : FileSystem | #fs.live > 2
}

run example for exactly 1 FileSystem, 4 FSObject
