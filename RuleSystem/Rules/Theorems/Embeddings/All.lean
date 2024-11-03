import RuleSystem.Rules.Theorems.Embeddings.Negative
import RuleSystem.Rules.Theorems.Embeddings.Positive

namespace Rule

-- 🔮 (EA-0)
theorem captureFromSingle_castSucc_subset_castSucc_captureFromSingle
    {n : ℕ}
    {rule : Rule n}
  : (rule.captureFromSingle |> Instances.castSucc) ⊆ rule.castSucc.captureFromSingle := by
    -- TODO: Do this 🟠
    -- TODO: Can we put this pattern of having a theorem for both positive and negative and then proving it for both
    --       cases into a helper?
    cases rule_eq : rule with
      | positive =>
        set rule' : Positive n := ⟨rule, isPositive_of_eq_positive rule_eq⟩
        subst rule
        exact @Positive.captureFromSingle_castSucc_subset_castSucc_captureFromSingle _ rule'
      | negative =>
        set rule' : Negative n := ⟨rule, isNegative_of_eq_negative rule_eq⟩
        subst rule
        exact @Negative.captureFromSingle_castSucc_subset_castSucc_captureFromSingle _ rule'

-- 🔮 (EA-1)
theorem captureFromSingle_castSucc_ssubset_castSucc_captureFromSingle
    {n : ℕ}
    {rule : Rule n}
  : (rule.captureFromSingle |> Instances.castSucc) ⊂ rule.castSucc.captureFromSingle := by
    cases rule_eq : rule with
      | positive =>
        set rule' : Positive n := ⟨rule, isPositive_of_eq_positive rule_eq⟩
        subst rule
        exact @Positive.captureFromSingle_castSucc_ssubset_castSucc_captureFromSingle _ rule'
      | negative =>
        set rule' : Negative n := ⟨rule, isNegative_of_eq_negative rule_eq⟩
        subst rule
        exact @Negative.captureFromSingle_castSucc_ssubset_castSucc_captureFromSingle _ rule'

-- 🔮 (EA-2)
theorem captureFromSingle_castSucc_eq_castSucc_captureFromSingle_sdiff_containingLast
    {n : ℕ}
    {rule : Rule n}
  : (rule.captureFromSingle |> Instances.castSucc) = rule.castSucc.captureFromSingle \ Instances.containingLast := by
    cases rule_eq : rule with
      | positive =>
        set rule' : Positive n := ⟨rule, isPositive_of_eq_positive rule_eq⟩
        subst rule
        exact @Positive.captureFromSingle_castSucc_eq_castSucc_captureFromSingle_sdiff_containingLast _ rule'
      | negative =>
        set rule' : Negative n := ⟨rule, isNegative_of_eq_negative rule_eq⟩
        subst rule
        exact @Negative.captureFromSingle_castSucc_eq_castSucc_captureFromSingle_sdiff_containingLast _ rule'

end Rule
