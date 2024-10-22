import RuleSystem.Rules.Positive
import RuleSystem.Rules.Negative

namespace Rule

theorem false_of_isPositive_of_isNegative
    {n : ℕ}
    {rule : Rule n}
    (h_pos : IsPositive rule)
    (h_neg : IsNegative rule)
  : False := by cases rule with
    | positive => exact h_neg
    | negative => exact h_pos

namespace Positive

theorem exists_val_eq_positive {n : ℕ} (rule : Positive n) : ∃ tags, rule.val = positive tags := by
  cases h : rule.val with
  | negative tags => exact False.elim (false_of_isPositive_of_isNegative rule.property (isNegative_of_eq_negative h))
  | positive tags => exists tags

theorem val_eq_positive {n : ℕ} (rule : Positive n) : rule.val = positive rule.val.tags := by
  obtain ⟨_, val_eq_positive⟩ := exists_val_eq_positive rule
  rw [val_eq_positive]
  rfl

end Positive

namespace Negative

theorem exists_val_eq_negative {n : ℕ} (rule : Negative n) : ∃ tags, rule.val = negative tags := by
  cases h : rule.val with
  | positive tags => exact False.elim (false_of_isPositive_of_isNegative (isPositive_of_eq_positive h) rule.property)
  | negative tags => exists tags

theorem val_eq_negative {n : ℕ} (rule : Negative n) : rule.val = negative rule.val.tags := by
  obtain ⟨_, val_eq_negative⟩ := exists_val_eq_negative rule
  rw [val_eq_negative]
  rfl

end Negative

end Rule
