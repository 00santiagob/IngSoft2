/*
	Practico 6
	Ejercicio 3
*/

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
	cache.addrs in main.addrs
}

pred Consistent [s: System] {
	s.cache.map - (s.cache.dirty -> Data) in s.main.map
}

pred Write [ m, m': Memory, a: Addr, d: Data ] {
	m'.map = m.map ++ (a -> d)
}

run Consistent for 1 System, 2 Memory, 2 Addr, 1 Data
run Write for 1 System, 2 Memory, 2 Addr, 2 Data

consistency: check {
	all s: System |
		all a: s.cache.addrs-s.cache.dirty |
			s.cache.map[a] = s.main.map[a]
} for 2
