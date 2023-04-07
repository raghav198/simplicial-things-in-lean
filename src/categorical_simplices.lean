import algebraic_topology.simplicial_object

open category_theory

lemma simplex_skeleton {n} : ulift (fin (n + 1)) = coe_sort (simplex_category.to_Cat.obj (simplex_category.mk n)) := rfl
def to_obj {n} (i : fin (n+1)) : simplex_category.to_Cat.obj (simplex_category.mk n) := (ulift.up i)
def to_hom {n} (i : fin n) : (to_obj i) ⟶ (to_obj i.succ) := begin
  unfold to_obj,
  apply ulift.up, apply plift.up,
  apply nat.le_of_lt, simp,
end

def point := @to_obj 0 0
def arrow := @to_hom 1 0
def triangle := (@to_hom 2 0, @to_hom 2 1)

lemma face_functor {n} (i : fin (n+2)) (j : fin (n+1)) : 
(simplex_category.to_Cat.map (simplex_category.δ i)).obj (to_obj j) = to_obj (fin.succ_above i j) := 
begin
  simp,
  dsimp [forget₂], dsimp [has_forget₂.forget₂],

  dsimp [to_obj],
  dsimp [simplex_category.hom.to_order_hom],
  dsimp [simplex_category.δ],
  dsimp [simplex_category.hom.mk],
  dsimp [order_hom_class.to_lattice_hom],
  dsimp [coe], dsimp [lift_t], unfold has_lift_t.lift,
  unfold coe_t, unfold has_coe_t.coe,

  unfold coe_fn, unfold has_coe_to_fun.coe, simp,
  unfold coe_fn, unfold has_coe_to_fun.coe, unfold fun_like.coe,
end