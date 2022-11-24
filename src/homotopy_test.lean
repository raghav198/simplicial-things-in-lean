import algebraic_topology.simplicial_set
import combinatorics.quiver.path
import simplicial_paths

open quiver

variable X : sSet

infix `**`:50 := path.comp

-- witnesses 0-simplices a, b as the boundary of 1-simplex ab
def ends (ab : X _[1]) (a b : X _[0]) := (X.δ 1 ab = a) ∧ (X.δ 0 ab = b)
-- produces a path a -> b given a proof that a, b are the boundary of a 1-simplex
def to_path {ab : X _[1]} {a b : X _[0]} (ε : ends X ab a b) :=
  edge_to_path ab a b ε.1 ε.2

-- triangle witnessing composition A -> B -> C = A -> C
lemma triangle (a b c : X _[0]) (ab bc ac : X _[1]) (abc : X _[2])
    {εab : ends X ab a b}  {εbc : ends X bc b c} {εac : ends X ac a c}
    {d0 : X.δ 0 abc = bc} {d1 : X.δ 1 abc = ac} {d2 : X.δ 2 abc = ab} :

    homotopic a c (to_path X εac) ((to_path X εab) ** (to_path X εbc)) :=
begin
    apply homotopic.lift, apply homotopic'.lift,
    subst d0, subst d1, subst d2,
    apply homotopic''.homotopy,
end

-- commutative square witnessing A -> B -> C = A -> D -> C = A -> C
lemma comm_square (a b c d : X _[0]) (ab bc ad dc ac : X _[1]) (abc adc : X _[2])
    {εab : ends X ab a b} {εbc : ends X bc b c} {εad : ends X ad a d}
    {εdc : ends X dc d c} {εac : ends X ac a c}
    {_ : X.δ 0 abc = bc} {_ : X.δ 1 abc = ac} {_ : X.δ 2 abc = ab}
    {_ : X.δ 0 adc = dc} {_ : X.δ 1 adc = ac} {_ : X.δ 2 adc = ad} :

    homotopic a c ((to_path X εab) ** (to_path X εbc)) ((to_path X εad) ** (to_path X εdc)) :=
begin
    apply homotopic.trans, apply homotopic.symm, 
    refine triangle X a b c ab bc ac abc; assumption,
    refine triangle X a d c ad dc ac adc; assumption,
end