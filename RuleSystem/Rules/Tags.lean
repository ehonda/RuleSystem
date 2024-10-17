import RuleSystem.Rules.Defs

namespace Tags

-- We need `n + 2` to have at least two tags
theorem exists_different_tag {n : ℕ} (tag : Tag (n + 2)) : ∃ tag', tag ≠ tag' := by
  cases tag with
    | mk k k_lt_n_plus_2 =>
      set k' := (k + 1) % (n + 2) with k'_def
      let k'_lt_n_plus_2 : k' < n + 2 := Nat.mod_lt _ (Nat.zero_lt_succ _)
      set tag' : Tag (n + 2) := ⟨k', k'_lt_n_plus_2⟩ with tag'_def
      exists tag'
      simp [tag'_def, k'_def]
      have : (k + 1) ≤ (n + 2) := Nat.add_one_le_iff.mpr k_lt_n_plus_2
      cases Nat.le_iff_lt_or_eq.mp this with
        | inl k'_lt_n_plus_2 =>
          have k'_mod_eq_k' := Nat.mod_eq_of_lt k'_lt_n_plus_2
          simp [k'_mod_eq_k']
        | inr k'_eq_n_plus_2 =>
          simp [k'_eq_n_plus_2, Nat.mod_self]
          intro k_eq_zero
          rw [k_eq_zero] at k'_eq_n_plus_2
          simp at k'_eq_n_plus_2

end Tags
