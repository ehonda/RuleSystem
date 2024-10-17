import RuleSystem.Rules.Defs

namespace Tags

-- We need `n + 2` to have at least two tags
-- theorem exists_different_tag {n : ℕ} (tag : Tag (n + 2)) : ∃ tag', tag ≠ tag'
--   := match tag with
--       | ⟨k, _⟩ =>
--         let k' := (k + 1) % (n + 2)
--         let k'_lt_n_plus_2 : k' < n + 2 := Nat.mod_lt _ (Nat.zero_lt_succ _)
--         let tag' := ⟨k', k'_lt_n_plus_2⟩
--         let tag_ne_tag' : tag ≠ tag' := by sorry
--         ⟨tag', tag_ne_tag'⟩
theorem exists_different_tag {n : ℕ} (tag : Tag (n + 2)) : ∃ tag', tag ≠ tag' := by
  cases tag with
    | mk k =>
      set k' := (k + 1) % (n + 2) with k'_def
      let k'_lt_n_plus_2 : k' < n + 2 := Nat.mod_lt _ (Nat.zero_lt_succ _)
      set tag' : Tag (n + 2) := ⟨k', k'_lt_n_plus_2⟩ with tag'_def
      exists tag'
      simp [tag'_def, k'_def]
      
      sorry

end Tags
