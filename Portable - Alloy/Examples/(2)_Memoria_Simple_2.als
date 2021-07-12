
open util/ordering [ System ] 

sig Addr, Data { }

sig Memory{
  addrs: set Addr
  map: Addr -> one Data
}{
  ~map.map in iden
  map.Data = addrs
}

sig MainMemory extends Memory {}

sig Cache extends Memory {
  dirty: set addrs
}

sig System {
  cache: Cache
  main: MainMemory
}

fact {
  all s:System | s.cache.addrs in s.main.addrs
}

pred write [ m,m': Memory, a: Addr, d: Data ]{
  m'.map = m.map ++ a -> d
}

pred read [ m: Memory, a: Addr, d: Data ] {
  let d' = m.map[a] | some d' implies d = d'
}

assert {
  all s: System |
    all a: s.cache.addrs - s.cache.dirty |
      s.cache.map[a] = s.main.map[a]
}
