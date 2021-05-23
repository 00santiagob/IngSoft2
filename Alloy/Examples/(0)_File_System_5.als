/*
	Tutorial: MIT - Alloy (5)
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

// Mover x al directorio d 
pred move [fs, fs': FileSystem, x: FSObject, d: Dir] {
	(x + d) in fs.live
	fs'.parent = fs.parent - x -> (x.(fs.parent)) + x -> d
}

// Elimina el archivo o directorio x 
pred remove [fs, fs': FileSystem, x: FSObject] {
	x in (fs.live - fs.root)
	fs'.root = fs.root
	fs'.parent = fs.parent - x -> (x.(fs.parent))
}

// Elimina recursivamente el objeto x 
pred removeAll [fs, fs': FileSystem, x: FSObject] {
	x in (fs.live - fs.root)
	fs'.root = fs.root
	let subtree = x.*(fs.contents) |
	fs'.parent = fs.parent - subtree -> (subtree.(fs.parent))
}

run move for 2 FileSystem, 4 FSObject
run remove for 2 FileSystem, 4 FSObject
run removeAll for 2 FileSystem, 4 FSObject

moveOkay: check {
	all fs, fs': FileSystem, x: FSObject, d:Dir |
		move[fs, fs', x, d] => fs'.live = fs.live
} for 5

// remove elimina exactamente el archivo o directorio especificado 
removeOkay: check {
	all fs, fs': FileSystem, x: FSObject |
		remove[fs, fs', x] => fs'.live = fs.live - x
} for 5

// removeAll elimina exactamente el subárbol especificado
removeAllOkay: check {
	all fs, fs': FileSystem, d: Dir |
		removeAll[fs, fs', d] => fs'.live = fs.live - d.*(fs.contents)
} for 5

// remove y removeAll tiene los mismos efectos en los archivos 
removeAllSame: check {
	all fs, fs1, fs2: FileSystem, f: File |
		remove[fs, fs1, f] && removeAll[fs, fs2, f] => fs1.live = fs2.live
} for 5