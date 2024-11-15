import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
import RuleSystem.Rules.Fin

namespace Finset

-- TODO: Why does this not exist in mathlib?
-- TODO: Is `α : Type*` correct or can we make it `α : Sort u`?
instance instCoeOutSubtype {α : Type*} {p : α → Prop} : CoeOut (Finset (Subtype p)) (Finset α) where
  coe := map (Function.Embedding.subtype _)

def castSucc {n : ℕ} (s : Finset (Fin n)) : Finset (Fin (n + 1)) := s.map Fin.castSuccEmb

def castSuccEmbedding {n : ℕ} : Finset (Fin n) ↪ Finset (Fin (n + 1))
  := ⟨castSucc, by simp [Function.Injective, castSucc]⟩

def CastPredPrecondition {n : ℕ} (s : Finset (Fin (n + 1))) := ∀ x ∈ s, x ≠ Fin.last _

-- Restrict `Fin.castPred` to members of `s` given `s.CastPredPrecondition`.
def restrictFinCastPred {n : ℕ} (s : Finset (Fin (n + 1))) (h : s.CastPredPrecondition) (x : s) : Fin n :=
  -- TODO: Why does this work but not the commented out version below?
  x.restrict (· ∈ s) Fin.castPred (h x x.property)
  -- Subtype.restrict (· ∈ s) (λ (y : s) ↦ Fin.castPred y (h y y.property)) x

def restrictFinCastPred_injective {n : ℕ} (s : Finset (Fin (n + 1))) (h : s.CastPredPrecondition)
  : Function.Injective (restrictFinCastPred s h) := by
    intro x y castPred_x_eq_castPred_y
    simp [restrictFinCastPred] at castPred_x_eq_castPred_y
    apply Subtype.eq
    exact Fin.castPred_inj.mp castPred_x_eq_castPred_y

def castPred {n : ℕ} (s : Finset (Fin (n + 1))) (h : s.CastPredPrecondition) : Finset (Fin n) :=
  -- TODO: Why does this work but not the commented out version below?
  Finset.univ.map ⟨restrictFinCastPred s h, restrictFinCastPred_injective s h⟩
  -- s.map ⟨restrictFinCastPred s h, restrictFinCastPred_injective s h⟩

abbrev HasCastPredPrecondition (n : ℕ) := Subtype (@CastPredPrecondition n)

-- TODO: Do we want to use this definition? It's certainly nicer to write down
def castPred' {n : ℕ} (s : HasCastPredPrecondition n) := castPred s.val s.property

theorem castPred_mem_iff_mem_castSucc
    {n : ℕ}
    {x : Fin (n + 1)}
    {x_ne_last : x ≠ Fin.last _}
    {s : Finset (Fin n)}
  : x.castPred x_ne_last ∈ s ↔ x ∈ s.castSucc := by
    simp [castSucc, Fin.castLE] at *
    constructor
    · intro
      exists x.castPred x_ne_last
    · intro x_mem_map_castSucc
      obtain ⟨_, _, _⟩ := x_mem_map_castSucc
      subst x
      assumption

theorem castSucc_mem_iff_mem_castPred
    {n : ℕ}
    {x : Fin n}
    {s : Finset (Fin (n + 1))}
    (s_castPredPrecondition : s.CastPredPrecondition)
  : x.castSucc ∈ s ↔ x ∈ s.castPred s_castPredPrecondition := by
    simp [castPred] at *
    constructor
    · intro x_castSucc_mem
      exists x.castSucc
      exists x_castSucc_mem
    · intro x_mem_map_castPred
      obtain ⟨_, _, _⟩ := x_mem_map_castPred
      subst x
      assumption

-- TODO: There should be an even more general version of this, find and prove it. Can we just use any embedding?
-- TODO: Naming
-- 🔮 (OF-0): `· · ↑ ↑`
theorem inter_eq_empty_iff_castSucc_inter_castSucc_eq_empty
    {n : ℕ}
    {s t : Finset (Fin n)}
  : s ∩ t = ∅ ↔ s.castSucc ∩ t.castSucc = ∅ := by
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
            simp [x_eq_last, castSucc, Fin.castSuccEmb] at x_mem_inter_map_castSuccEmb
            obtain ⟨⟨_, _, castLE_eq_last⟩, _⟩ := x_mem_inter_map_castSuccEmb
            exact Fin.false_of_castLE_eq_last castLE_eq_last
          set x' := x.castPred x_ne_last with x'_def
          have x'_mem_inter : x' ∈ s ∩ t := by
            simp [x'_def]
            constructor
            · apply castPred_mem_iff_mem_castSucc.mpr
              exact (Finset.mem_inter.mp x_mem_inter_map_castSuccEmb).left
            · apply castPred_mem_iff_mem_castSucc.mpr
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
      have x'_mem_inter_castSucc : x' ∈ (s.castSucc ∩ t.castSucc) := by
        apply Finset.mem_inter_of_mem
        · simp [castSucc, x'_def, Fin.castSucc, Fin.castAdd]
          exact Finset.mem_of_mem_inter_left x_mem_inter
        · simp [castSucc, x'_def, Fin.castSucc, Fin.castAdd]
          exact Finset.mem_of_mem_inter_right x_mem_inter
      simp [inter_map_castSuccEmb_eq_empty] at x'_mem_inter_castSucc

-- TODO: There should be an even more general version of this, find and prove it. Can we just use any embedding and it's
--       "inverse" in the sense that `castPred` is an inverse here
-- TODO: Naming
-- TODO: Formulate with `castPred'`
-- 🔮 (OF-1): `· ↓ ↑ ·`
theorem inter_castPred_eq_empty_iff_castSucc_inter_eq_empty
    {n : ℕ}
    {s : Finset (Fin n)}
    {t : Finset (Fin (n + 1))}
    (t_castPredPrecondition : t.CastPredPrecondition)
  : s ∩ (t.castPred t_castPredPrecondition) = ∅ ↔ s.castSucc ∩ t = ∅ := by
    -- TODO: Very similar to above, maybe we can factor out common stuff
    constructor
    · intro inter_castPred_eq_empty
      by_contra castSucc_inter_ne_empty
      obtain ⟨x, x_mem_castSucc_inter⟩ := Finset.nonempty_of_ne_empty castSucc_inter_ne_empty
      have x_ne_last : x ≠ Fin.last _ := by
        intro x_eq_last
        simp [x_eq_last, castSucc] at x_mem_castSucc_inter
        obtain ⟨⟨_, _, castLE_eq_last⟩, _⟩ := x_mem_castSucc_inter
        exact Fin.false_of_castLE_eq_last castLE_eq_last
      set x' := x.castPred x_ne_last with x'_def
      have x'_mem_inter_castPred : x' ∈ s ∩ (t.castPred t_castPredPrecondition) := by
        simp [x'_def]
        constructor
        · apply castPred_mem_iff_mem_castSucc.mpr
          exact (Finset.mem_inter.mp x_mem_castSucc_inter).left
        · simp [castPred, restrictFinCastPred, Subtype.restrict]
          exists x
          exists (Finset.mem_inter.mp x_mem_castSucc_inter).right
      simp [inter_castPred_eq_empty] at x'_mem_inter_castPred
    · intro castSucc_inter_eq_empty
      by_contra inter_castPred_ne_empty
      obtain ⟨x, x_mem_inter_castPred⟩ := Finset.nonempty_of_ne_empty inter_castPred_ne_empty
      set x' := x.castSucc with x'_def
      have x'_mem_castSucc_inter : x' ∈ (s.castSucc ∩ t) := by
        apply Finset.mem_inter_of_mem
        · simp [castSucc, x'_def, Fin.castSucc, Fin.castAdd]
          exact Finset.mem_of_mem_inter_left x_mem_inter_castPred
        · simp [x'_def]
          apply (castSucc_mem_iff_mem_castPred t_castPredPrecondition).mpr
          exact Finset.mem_of_mem_inter_right x_mem_inter_castPred
      simp [castSucc_inter_eq_empty] at x'_mem_castSucc_inter

end Finset
