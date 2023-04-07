-- literally only doing this to have a version of quiver that category doesn't extend
-- because dealing with that is my personal hell

import algebraic_topology.simplicial_set

universe u

variable {X : sSet.{u}}

notation (name := simplicial_object.at) X ` _[`:1000 n `]` :=
  (X : category_theory.simplicial_object hole!).obj (opposite.op (simplex_category.mk n))

-- witnesses 0-simplices a, b as the boundary of 1-simplex ab
def ends (ab : X _[1]) (a b : X _[0]) := (X.δ 1 ab = a) ∧ (X.δ 0 ab = b)
def qedge (A B : X _[0]) := {e : X _[1] // ends e A B}

infixr ` ->- `:10 := qedge

inductive path (a : X _[0]) : X _[0] → Type u
| nil : path a
| cons : Π {b c : X _[0]}, path b → (b ->- c) → path c

variables (A B : X _[0]) (e : A ->- B)
#check (coe e : X _[1])

namespace path

end path