/*
	Practico 6
	Ejercicio 4
*/

sig Node {} // Vertice
sig Graph {	// Grafo
	nodes: set Node, // Conjunto de nodos
	edges: Node -> Node // Conjunto de aristas
}{
	all n: Node | n in nodes // Todo nodo pertenece al grafo
	no (iden & (Node -> Node) & edges) // No hay reflexividad
}

// Ejercicio 4 - a)
pred aciclico[g:Graph]{
	no v: Node |
		(v-> Node) + (Node -> v) in *(g.edges)
}

// Ejercicio 4 - b)
pred no_dirigido[g:Graph]{
	g.edges = ~(g.edges)
}

// Ejercicio 4 - c)
pred fuertemente_conexo[g:Graph]{}

// Ejercicio 4 - d)
pred conexo[g:Graph]{}

run aciclico for 5 Node, 1 Graph
run no_dirigido for 5 Node, 1 Graph
run fuertemente_conexo for 5 Node, 1 Graph
run conexo for 5 Node, 1 Graph
