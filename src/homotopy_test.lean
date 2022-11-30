import algebraic_topology.simplicial_set
import combinatorics.quiver.path
import path_homotopy

open quiver

variable {X : sSet}


-- triangle witnessing composition A -> B -> C = A -> C
lemma triangle (a b c : X _[0]) (ab bc ac : X _[1]) (abc : X _[2])
    {εab : ends ab a b}  {εbc : ends bc b c} {εac : ends ac a c}
    {d0 : X.δ 0 abc = bc} {d1 : X.δ 1 abc = ac} {d2 : X.δ 2 abc = ab} :

    homotopic a c (to_path εac) ((to_path εab) ** (to_path εbc)) :=
begin
    apply homotopic.lift,
    subst d0, subst d1, subst d2,
    apply homotopic''.homotopy,
end

-- commutative square witnessing A -> B -> C = A -> D -> C = A -> C
lemma comm_square (a b c d : X _[0]) (ab bc ad dc ac : X _[1]) (abc adc : X _[2])
    {εab : ends ab a b} {εbc : ends bc b c} {εad : ends ad a d}
    {εdc : ends dc d c} {εac : ends ac a c}
    {_ : X.δ 0 abc = bc} {_ : X.δ 1 abc = ac} {_ : X.δ 2 abc = ab}
    {_ : X.δ 0 adc = dc} {_ : X.δ 1 adc = ac} {_ : X.δ 2 adc = ad} :

    homotopic a c ((to_path εab) ** (to_path εbc)) ((to_path εad) ** (to_path εdc)) :=
begin
    apply homotopic.trans, apply homotopic.symm, 
    refine triangle a b c ab bc ac abc; assumption,
    refine triangle a d c ad dc ac adc; assumption,
end


lemma two_triangles (a b c d e : X _[0]) (ab bc ac cd de ce : X _[1]) (abc cde : X _[2])
    {εab : ends ab a b} {εbc : ends bc b c} {εac : ends ac a c}
    {εcd : ends cd c d} {εde : ends de d e} {εce : ends ce c e}

    {_ : X.δ 0 abc = bc} {_ : X.δ 1 abc = ac} {_ : X.δ 2 abc = ab}
    {_ : X.δ 0 cde = de} {_ : X.δ 1 cde = ce} {_ : X.δ 2 cde = cd} :

    homotopic a e ((to_path εac) ** (to_path εce)) ((to_path εab) ** (to_path εbc) ** (to_path εcd) ** (to_path εde)) :=
begin
  have H1 : homotopic a e ((to_path εac) ** (to_path εce)) ((to_path εab) ** (to_path εbc) ** (to_path εce)),
  apply homotopic.comp_r,
  refine triangle a b c ab bc ac abc; assumption,
  
  have H2 : homotopic a e ((to_path εab) ** (to_path εbc) ** (to_path εce)) ((to_path εab) ** (to_path εbc) ** (to_path εcd) ** (to_path εde)),
  rw path.comp_assoc (to_path εab**to_path εbc),
  apply homotopic.comp_l,
  refine triangle c d e cd de ce cde; assumption,
  
  apply homotopic.trans, refine H1, refine H2,
end