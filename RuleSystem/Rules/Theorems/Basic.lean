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

theorem tags_eq_of_eq {n : ℕ} {rule rule' : Rule n} (h : rule = rule') : rule.tags = rule'.tags := by
  simp [Rule.tags, h]

namespace Positive

theorem exists_val_eq_positive {n : ℕ} (rule : Positive n) : ∃ tags, rule.val = positive tags := by
  cases h : rule.val with
  | negative tags => exact False.elim (false_of_isPositive_of_isNegative rule.property (isNegative_of_eq_negative h))
  | positive tags => exists tags

theorem val_eq_positive {n : ℕ} (rule : Positive n) : rule.val = positive rule.val.tags := by
  obtain ⟨_, val_eq_positive⟩ := exists_val_eq_positive rule
  rw [val_eq_positive]
  rfl

theorem eq_iff_tags_eq {n : ℕ} {rule rule' : Positive n} : rule = rule' ↔ rule.val.tags = rule'.val.tags := by
  constructor
  · intro rule_eq_rule'
    simp [Rule.tags, rule_eq_rule']
  · intro rule_tags_eq_rule'_tags
    obtain ⟨tags, rule_val_eq_positive⟩ := exists_val_eq_positive rule
    obtain ⟨tags', rule'_val_eq_positive⟩ := exists_val_eq_positive rule'
    simp [Rule.tags, rule_val_eq_positive, rule'_val_eq_positive] at rule_tags_eq_rule'_tags
    apply Subtype.eq_iff.mpr
    simp [rule_val_eq_positive, rule'_val_eq_positive, rule_tags_eq_rule'_tags]

theorem eq_fromTags_iff_tags_eq
    {n : ℕ}
    {tags : Tags n}
    {rule : Positive n}
  : rule = fromTags tags ↔ rule.val.tags = tags := by
    constructor
    · intro rule_eq_fromTags
      simp [Rule.tags, rule_eq_fromTags, fromTags]
    -- TODO: Find a better proof
    · intro rule_val_tags_eq_tags
      apply Subtype.eq_iff.mpr
      simp [rule_val_tags_eq_tags, fromTags]
      obtain ⟨tags', rule_val_eq_positive⟩ := exists_val_eq_positive rule
      simp [rule_val_eq_positive] at *
      exact rule_val_tags_eq_tags

-- rule_val_ne_untagged : rule ≠ untagged n
theorem ne_untagged_iff_val_tags_nonempty {n : ℕ} {rule : Positive n}
  : rule ≠ untagged n ↔ rule.val.tags.Nonempty := by
    constructor
    · intro rule_ne_untagged
      -- TODO: There's got to be a simpler way to do this
      apply Decidable.byContradiction
      intro tags_eq_empty
      simp at tags_eq_empty
      have : rule = untagged n := by
        apply eq_fromTags_iff_tags_eq.mpr
        assumption
      contradiction
    · intro rule_val_tags_nonempty rule_eq_untagged
      obtain ⟨tag, tag_mem_rule_tags⟩ := rule_val_tags_nonempty
      subst rule
      simp [untagged_val_tags_eq_empty] at tag_mem_rule_tags

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

theorem eq_iff_tags_eq {n : ℕ} {rule rule' : Negative n} : rule = rule' ↔ rule.val.tags = rule'.val.tags := by
  constructor
  · intro rule_eq_rule'
    simp [Rule.tags, rule_eq_rule']
  · intro rule_tags_eq_rule'_tags
    obtain ⟨tags, rule_val_eq_negative⟩ := exists_val_eq_negative rule
    obtain ⟨tags', rule'_val_eq_negative⟩ := exists_val_eq_negative rule'
    simp [Rule.tags, rule_val_eq_negative, rule'_val_eq_negative] at rule_tags_eq_rule'_tags
    apply Subtype.eq_iff.mpr
    simp [rule_val_eq_negative, rule'_val_eq_negative, rule_tags_eq_rule'_tags]

theorem eq_fromTags_iff_tags_eq
    {n : ℕ}
    {tags : Tags n}
    {rule : Negative n}
  : rule = fromTags tags ↔ rule.val.tags = tags := by
    constructor
    · intro rule_eq_fromTags
      simp [Rule.tags, rule_eq_fromTags, fromTags]
    -- TODO: Find a better proof
    · intro rule_val_tags_eq_tags
      apply Subtype.eq_iff.mpr
      simp [rule_val_tags_eq_tags, fromTags]
      obtain ⟨tags', rule_val_eq_negative⟩ := exists_val_eq_negative rule
      simp [rule_val_eq_negative] at *
      exact rule_val_tags_eq_tags

end Negative

end Rule
