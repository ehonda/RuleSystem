-- We don't even need this do we? We just use `BigOr_exists_eq` all the time

-- TODO: Better name
def BigOr (ps : List Prop) : Prop := ps.foldl Or False

theorem BigOr_cons_of_BigOr {p : Prop} {ps : List Prop} : BigOr ps → BigOr (p :: ps) := by
  simp only [BigOr, List.foldl_cons, false_or]
  cases ps with
    | nil => exact False.elim
    | cons p' ps =>
      simp only [List.foldl, false_or, List.foldl_assoc]
      exact Or.inr

-- TODO: Better name
theorem BigOr_iff {p : Prop} {ps : List Prop} : BigOr (p :: ps) ↔ p ∨ BigOr ps := by
  simp [BigOr]
  cases ps with
    | nil => simp only [List.foldl, or_false]
    | cons p' ps => simp only [List.foldl, List.foldl_assoc, false_or]

-- TODO: Better name
theorem BigOr_eq {p : Prop} {ps : List Prop} : (BigOr (p :: ps)) = (p ∨ BigOr ps)
  := propext BigOr_iff

theorem BigOr_iff_exists {ps : List Prop} : BigOr ps ↔ ∃ p, p ∈ ps ∧ p := by
  simp [BigOr]
  -- TODO: `induction` or `cases`?
  induction ps with
    | nil => simp only [List.foldl, List.not_mem_nil, false_and, exists_const]
    | cons p ps ih =>
      simp [List.foldl, List.foldl_assoc]
      constructor
      · sorry
      · sorry

theorem BigOr_exists_eq {ps : List Prop} : BigOr ps = ∃ p, p ∈ ps ∧ p
  := propext BigOr_iff_exists
