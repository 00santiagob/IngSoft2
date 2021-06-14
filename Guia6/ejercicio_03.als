/*
	Practico 6
	Ejercicio 3
*/

open util/ordering[System]

sig Addr, Data {}

sig Memory {
	addrs: set Addr,
	map: Addr -> lone Data
}{
	~map.map in iden
	map.Data = addrs
}

sig MainMemory extends Memory {}

sig Cache extends Memory {
	dirty: set addrs
}

sig System {
	cache: Cache,
	main: MainMemory
}{
	main.addrs = Addr // Quiero que toda direccion pertenesca a la memoria principal.
	cache.addrs in main.addrs
	cache.dirty in cache.addrs
}

pred Consistent [ s: System ] {
	s.cache.map - (s.cache.dirty -> Data) in s.main.map
}

pred Write [ m, m': Memory, a: Addr, d: Data ] {
	m'.map = m.map ++ (a -> d)
}

pred Flush [ s, s': System ] {
	(s != s') &&
	(all a: s.cache.dirty |
		(s'.main.map = s.main.map ++ (a -> s.cache.map[a])) &&
		(s'.cache.map = s.cache.map - (a -> s.cache.map[a]))
	) &&
	(s'.cache.dirty = none)
}

fact Flushing {
	all s: System, s' : next[s] | 
		(s.cache.dirty != none) => Flush[s, s']
}

pred Load [ s: System ] {}

pred show[ s: System ] {
	some s: System | Consistent[s] && s.cache.dirty = none
}

run Consistent for 1 System, 2 Memory, 4 Addr, 3 Data
run Write for 1 System, 2 Memory, 4 Addr, 3 Data
run Flush for 2 System, 2 Memory, 2 Addr, 4 Data
run Load for 1 System, 2 Memory, 4 Addr, 3 Data
run show for 2

consistency: check {
	all s: System |
		all a: s.cache.addrs-s.cache.dirty |
			s.cache.map[a] = s.main.map[a]
} for 2
