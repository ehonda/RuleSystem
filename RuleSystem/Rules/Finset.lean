import Mathlib.Data.Finset.Image
import RuleSystem.Rules.Fin

namespace Finset

-- TODO: Why does this not exist in mathlib?
-- TODO: Is `α : Type*` correct or can we make it `α : Sort u`?
instance instCoeOutSubtype {α : Type*} {p : α → Prop} : CoeOut (Finset (Subtype p)) (Finset α) where
  coe := map (Function.Embedding.subtype _)

theorem castPred_mem_iff_mem_map_castSuccEmb
    {n : ℕ}
    {x : Fin (n + 1)}
    {x_ne_last : x ≠ Fin.last _}
    {s : Finset (Fin n)}
  : x.castPred x_ne_last ∈ s ↔ x ∈ s.map Fin.castSuccEmb := by
    simp [Fin.castLE] at *
    constructor
    · intro
      exists x.castPred x_ne_last
    · intro x_mem_map_castSuccEmb
      obtain ⟨_, _, _⟩ := x_mem_map_castSuccEmb
      subst x
      assumption

-- TODO: There should be a more general version of this, find and prove it
-- TODO: Naming
-- tags_inter_inst'_tags_eq_empty : tags ∩ inst'.tags = ∅
-- ⊢ Finset.map Fin.castSuccEmb tags ∩ Finset.map Fin.castSuccEmb inst'.tags = ∅
theorem inter_eq_empty_iff_inter_map_castSuccEmb_eq_empty
    {n : ℕ}
    {s t : Finset (Fin n)}
  : s ∩ t = ∅ ↔ s.map Fin.castSuccEmb ∩ t.map Fin.castSuccEmb = ∅ := by
    constructor
    -- TODO: Maybe there's an easier way, this is all very technical
    · intro inter_eq_empty
      by_contra inter_map_castSuccEmb_ne_empty
      set r := (s.map Fin.castSuccEmb ∩ t.map Fin.castSuccEmb) \ {Fin.last n} with r_def
      cases Decidable.eq_or_ne r ∅ with
        | inl r_eq_empty =>
          obtain ⟨x, x_mem_inter_map_castSuccEmb⟩ := Finset.nonempty_of_ne_empty inter_map_castSuccEmb_ne_empty
          have x_ne_last : x ≠ Fin.last n := by
            intro x_eq_last
            simp [x_eq_last, Fin.castSuccEmb] at x_mem_inter_map_castSuccEmb
            obtain ⟨⟨_, _, castLE_eq_last⟩, _⟩ := x_mem_inter_map_castSuccEmb
            exact Fin.false_of_castLE_eq_last castLE_eq_last
          set x' := x.castPred x_ne_last with x'_def
          have x'_mem_inter : x' ∈ s ∩ t := by
            simp [x'_def]
            constructor
            · apply castPred_mem_iff_mem_map_castSuccEmb.mpr
              exact (Finset.mem_inter.mp x_mem_inter_map_castSuccEmb).left
            · apply castPred_mem_iff_mem_map_castSuccEmb.mpr
              exact (Finset.mem_inter.mp x_mem_inter_map_castSuccEmb).right
          simp [inter_eq_empty] at x'_mem_inter
        | inr r_ne_empty =>
          obtain ⟨x, x_mem_r⟩ := Finset.nonempty_of_ne_empty r_ne_empty
          simp [r_def] at x_mem_r
          have x_ne_last : x ≠ Fin.last n := by
            obtain ⟨_, _⟩ := x_mem_r
            assumption
          set x' := x.castPred x_ne_last with x'_def
          have x'_mem_inter : x' ∈ s ∩ t := by
            simp [x'_def]
            constructor
            · obtain ⟨⟨⟨_, _, _⟩, _⟩, _⟩ := x_mem_r
              subst x
              simpa [Fin.castPred, Fin.castLE]
            · obtain ⟨⟨_, ⟨_, _, _⟩⟩, _⟩ := x_mem_r
              subst x
              simpa [Fin.castPred, Fin.castLE]
          simp [inter_eq_empty] at x'_mem_inter
    · intro inter_map_castSuccEmb_eq_empty
      by_contra inter_ne_empty
      obtain ⟨x, x_mem_inter⟩ := Finset.nonempty_of_ne_empty inter_ne_empty
      set x' := x.castSucc with x'_def
      have x'_mem_map_castSuccEmb : x' ∈ (s.map Fin.castSuccEmb ∩ t.map Fin.castSuccEmb) := by
        apply Finset.mem_inter_of_mem
        · simp [x'_def, Fin.castSucc, Fin.castAdd]
          exact Finset.mem_of_mem_inter_left x_mem_inter
        · simp [x'_def, Fin.castSucc, Fin.castAdd]
          exact Finset.mem_of_mem_inter_right x_mem_inter
      simp [inter_map_castSuccEmb_eq_empty] at x'_mem_map_castSuccEmb

end Finset
