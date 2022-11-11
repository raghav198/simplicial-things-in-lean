import topology.constructions
import topology.separation
import topology.category.Top.basic
import topology.homotopy.basic
import analysis.convex.star

lemma quotient_map_of_is_closed_map {α β} [topological_space α] [topological_space β]
  (f : α → β) : function.surjective f → is_closed_map f → continuous f → quotient_map f :=

begin
  intros hS hC hCont,
  rw quotient_map_iff,
  split, assumption, 
  intro U,
  rw [← is_closed_compl_iff, ← is_closed_compl_iff, ← set.preimage_compl],
  generalize : Uᶜ = C,
end