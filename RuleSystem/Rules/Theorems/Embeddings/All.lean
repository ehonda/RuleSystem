import RuleSystem.Rules.Theorems.Embeddings.Negative
import RuleSystem.Rules.Theorems.Embeddings.Positive

namespace Rule

-- 🔮 (EA-0)
-- Deprecated, just left in for demo purposes for now
-- TODO: Remove
theorem captureFromSingle_castSucc_subset_castSucc_captureFromSingle
    {n : ℕ}
    {rule : Rule n}
  : (rule.captureFromSingle |> Instances.castSucc) ⊆ rule.castSucc.captureFromSingle := by
    cases rule_eq : rule with
      | positive =>
        set rule' : Positive n := ⟨rule, isPositive_of_eq_positive rule_eq⟩
        subst rule
        exact @Positive.captureFromSingle_castSucc_subset_castSucc_captureFromSingle _ rule'
      | negative =>
        set rule' : Negative n := ⟨rule, isNegative_of_eq_negative rule_eq⟩
        subst rule
        exact @Negative.captureFromSingle_castSucc_subset_castSucc_captureFromSingle _ rule'

-- 🔮 (EA-0')
-- Deprecated, just left in for demo purposes for now
-- TODO: Remove
theorem captureFromSingle_castSucc_subset_castSucc_captureFromSingle'
    {n : ℕ}
    {rule : Rule n}
  : (rule.captureFromSingle |> Instances.castSucc) ⊆ rule.castSucc.captureFromSingle :=
    let h := λ (rule' : Rule n) ↦ (rule'.captureFromSingle |> Instances.castSucc) ⊆ rule'.castSucc.captureFromSingle
    let h_pos := λ (rule' : Positive n) ↦ @Positive.captureFromSingle_castSucc_subset_castSucc_captureFromSingle _ rule'
    let h_neg := λ (rule' : Negative n) ↦ @Negative.captureFromSingle_castSucc_subset_castSucc_captureFromSingle _ rule'
    of_forall_positive_of_forall_negative h h_pos h_neg

-- 🔮 (EA-0'')
-- This is pretty nice usability wise
theorem captureFromSingle_castSucc_subset_castSucc_captureFromSingle''
    {n : ℕ}
    {rule : Rule n}
  : (rule.captureFromSingle |> Instances.castSucc) ⊆ rule.castSucc.captureFromSingle := by
    let h := λ (rule' : Rule n) ↦ (rule'.captureFromSingle |> Instances.castSucc) ⊆ rule'.castSucc.captureFromSingle
    apply of_forall_positive_of_forall_negative h
    · apply Positive.captureFromSingle_castSucc_subset_castSucc_captureFromSingle
    · apply Negative.captureFromSingle_castSucc_subset_castSucc_captureFromSingle

-- 🔮 (EA-1)
theorem captureFromSingle_castSucc_ssubset_castSucc_captureFromSingle
    {n : ℕ}
    {rule : Rule n}
  : (rule.captureFromSingle |> Instances.castSucc) ⊂ rule.castSucc.captureFromSingle := by
    let h := λ (rule' : Rule n) ↦ (rule'.captureFromSingle |> Instances.castSucc) ⊂ rule'.castSucc.captureFromSingle
    apply of_forall_positive_of_forall_negative h
    · apply Positive.captureFromSingle_castSucc_ssubset_castSucc_captureFromSingle
    · apply Negative.captureFromSingle_castSucc_ssubset_castSucc_captureFromSingle

-- 🔮 (EA-2)
theorem captureFromSingle_castSucc_eq_castSucc_captureFromSingle_sdiff_containingLast
    {n : ℕ}
    {rule : Rule n}
  : (rule.captureFromSingle |> Instances.castSucc) = rule.castSucc.captureFromSingle \ Instances.containingLast := by
    let h := λ (rule' : Rule n) ↦ (rule'.captureFromSingle |> Instances.castSucc) = rule'.castSucc.captureFromSingle \ Instances.containingLast
    apply of_forall_positive_of_forall_negative h
    · apply Positive.captureFromSingle_castSucc_eq_castSucc_captureFromSingle_sdiff_containingLast
    · apply Negative.captureFromSingle_castSucc_eq_castSucc_captureFromSingle_sdiff_containingLast

end Rule
