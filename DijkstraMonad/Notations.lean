import DijkstraMonad.Basic
import DijkstraMonad.Id
import DijkstraMonad.State
import DijkstraMonad.Read
import DijkstraMonad.Except

open EffectObservation
open OrderedMonad
open DijkstraMonad


#check inferInstanceAs (DijkstraMonad Id.wp (ToDMonad Id Id.wp))

declare_syntax_cat dijkstra_do
declare_syntax_cat dijkstra_singleton

syntax term " with " term " using " term : dijkstra_singleton
syntax term : dijkstra_singleton

syntax "let" ident " <- " dijkstra_singleton " ; " dijkstra_do : dijkstra_do
syntax "let" ident " ← " dijkstra_singleton " ; " dijkstra_do : dijkstra_do
syntax "let" ident " := " term " ; " dijkstra_do : dijkstra_do
syntax "with" term " using " term " ; " dijkstra_do : dijkstra_do
syntax dijkstra_singleton : dijkstra_do
syntax dijkstra_singleton " ; " dijkstra_do : dijkstra_do

syntax "Do { " dijkstra_do " } " : term
syntax "DoSing { " dijkstra_singleton " } " : term

#check compD

#check fun i:Nat => i

macro_rules
| `(DoSing { $t:term }) =>
  `($t)
| `(DoSing { $t1:term with $t2:term using $t3:term }) =>
  `(@DijkstraMonad.compD _ _ _ _ _ _ $t2 _ $t1 $t3)

macro_rules
| `(Do { let $id:ident ← $t1:dijkstra_singleton ; $dd:dijkstra_do }) =>
  `(DijkstraMonad.bindD (DoSing { $t1 }) fun $id => Do { $dd })

| `(Do { let $id:ident <- $t1:dijkstra_singleton ; $dd:dijkstra_do }) =>
  `(Do { let $id ← $t1 ; $dd })

| `(Do { let $id:ident := $t1:term ; $dd:dijkstra_do}) =>
  `((let $id := $t1; Do { $dd }))

| `(Do { with $t1:term using $t2:term ; $dd:dijkstra_do }) =>
  `(@DijkstraMonad.compD _ _ _ _ _ _ $t1 _ (Do { $dd }) $t2)

| `(Do { $t:dijkstra_singleton; $dd:dijkstra_do }) =>
  `(DijkstraMonad.bindD (DoSing {$t}) fun _ => Do { $dd } )

| `(Do { $t:dijkstra_singleton }) =>
  `(DoSing {$t})
