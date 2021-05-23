// Imponer un ordenamiento al Estado
open util/ordering[State] 

// Granjero y sus posesiones son objetos.
abstract sig Object { eats: set Object }
one sig Farmer, Fox, Chicken, Grain extends Object {}

//  Define qué come qué y el agricultor no está cerca.
fact eating {
	eats = Fox -> Chicken + Chicken -> Grain
}

// Almacena los objetos en el lado cercano y lejano del río.
sig State {
	near, far: set Object
} 

// En el estado inicial, todos los objetos están en el lado cercano
fact initialState {
	first[].near = Object && no first[].far 
}

// Como máximo un elemento para mover de 'desde' a 'a'
pred crossRiver [ from, from', to, to': set Object ] { 
	( from' = from - Farmer && to' = to - to.eats + Farmer) 
	||
	( some item: from - Farmer |
		from' = from - Farmer - item &&
		to' = to - to.eats + Farmer + item
		)
	} 

// Transiciones crossRiver entre estados
fact stateTransition {
	all s: State, s': next[s] |
		( Farmer in s.near => crossRiver [ s.near, s'.near, s.far, s'.far ] ) &&
		( Farmer in s.far => crossRiver [ s.far, s'.far, s.near, s'.near ] )
}

// El granjero mueve todo al otro lado del río
pred solvePuzzle[] {
	last[].far = Object 
}

// Ejecución
run solvePuzzle for 8 State 
