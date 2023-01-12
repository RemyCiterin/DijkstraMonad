import DijkstraMonad.Id

#check inferInstanceAs (DijkstraMonad Id.wp (ToDMonad Id Id.wp))

declare_syntax_cat dijkstra_do

syntax "let" ident " ← " term " ; " dijkstra_do : dijkstra_do
syntax "let" ident " := " term " ; " dijkstra_do : dijkstra_do
syntax term : dijkstra_do

syntax "Do { " dijkstra_do " } " : term

macro_rules
| `(Do { let $id:ident ← $t1:term ; $dd:dijkstra_do }) => `(DijkstraMonad.bindD $t1 fun $id => Do { $dd })
| `(Do { let $id:ident := $t1:term ; $dd:dijkstra_do}) => `(let $id := $t1; Do { $dd })
| `(Do { $t:term }) => `($t)

#check DijkstraMonad.bindD

def test : ToDMonad Id Id.wp Nat (pure 1) := DijkstraMonad.pureD 1
def test1 (i:Nat) : ToDMonad Id Id.wp Nat (pure (.succ i)) := DijkstraMonad.pureD (i + 1)

def test' : ToDMonad Id Id.wp Nat (pure 2) := Do {
  let i ← test;
  test1 i
}
