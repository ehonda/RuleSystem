import RuleSystem.Rules.Theorems.Advanced

namespace Rule

namespace Negative

theorem capture_eq_captureOnTagged_union_singleton_untagged
    {n : ℕ}
    (rule : Negative n)
  : capture {rule.val} = captureOnTagged {rule.val} ∪ {Instance.untagged} := by
    ext inst
    obtain ⟨tags, rule_val_eq⟩ := Negative.exists_val_eq_negative rule
    simp [capture, captureOnTagged, applyTo, appliesTo, rule_val_eq]
    constructor
    · intro tags_inter_inst_tags_eq_empty
      -- TODO: Maybe there's a more elegant way to do this
      cases Decidable.eq_or_ne inst.tags ∅ with
        | inl inst_tags_eq_empty =>
          right
          simp [Instance.untagged, inst_tags_eq_empty]
          apply Instance.eq_mk_iff_tags_eq.mpr
          assumption
        | inr tags_ne_empty =>
          left
          constructor
          · assumption
          · apply Finset.nonempty_of_ne_empty
            assumption
    · intro inst_mem_captureOnTagged_or_inst_eq_untagged
      cases inst_mem_captureOnTagged_or_inst_eq_untagged with
        | inl inst_mem_captureOnTagged => exact inst_mem_captureOnTagged.left
        | inr inst_eq_untagged => simp [inst_eq_untagged, Instance.untagged]

-- TODO: eq iff

end Negative

namespace Positive

-- TODO: eq iff

theorem capture_subset_captureOnTagged_union_singleton_untagged
    {n : ℕ}
    (rule : Positive n)
  : capture {rule.val} ⊆ captureOnTagged {rule.val} ∪ {Instance.untagged} := by
    intro inst
    obtain ⟨tags, rule_val_eq⟩ := Positive.exists_val_eq_positive rule
    simp [capture, captureOnTagged, applyTo, appliesTo, rule_val_eq]
    intro tags_sub_inst_tags
    cases Decidable.eq_or_ne inst.tags ∅ with
      | inl inst_tags_eq_empty =>
        right
        simp [Instance.untagged, inst_tags_eq_empty]
        apply Instance.eq_mk_iff_tags_eq.mpr
        assumption
      | inr tags_ne_empty =>
        left
        constructor
        · assumption
        · apply Finset.nonempty_of_ne_empty
          assumption

theorem capture_eq_captureOnTagged_union_singleton_untagged_of_eq_untagged
    {n : ℕ}
    (rule : Positive n)
    (rule_eq_untagged : rule = Positive.untagged n)
  : capture {rule.val} = captureOnTagged {rule.val} ∪ {Instance.untagged} := by
    ext inst
    constructor
    · apply capture_subset_captureOnTagged_union_singleton_untagged
    · intro inst_mem_captureOnTagged_or_inst_eq_untagged
      simp at inst_mem_captureOnTagged_or_inst_eq_untagged
      cases inst_mem_captureOnTagged_or_inst_eq_untagged with
        | inl inst_mem_captureOnTagged =>
          simp [captureOnTagged] at inst_mem_captureOnTagged
          exact inst_mem_captureOnTagged.left
        | inr inst_eq_untagged =>
          simp [
            inst_eq_untagged, Instance.untagged, rule_eq_untagged, untagged, fromTags, capture, applyTo, appliesTo]

theorem capture_eq_captureOnTagged_of_tags_nonempty
    {n : ℕ}
    {rule : Positive n}
    (rule_val_tags_nonempty : rule.val.tags.Nonempty)
  : capture {rule.val} = captureOnTagged {rule.val} := by
    ext inst
    obtain ⟨tags, rule_val_eq⟩ := Positive.exists_val_eq_positive rule
    simp [capture, captureOnTagged, applyTo, appliesTo, rule_val_eq]
    intro tags_sub_inst_tags
    obtain ⟨tag, tag_mem_rule_tags⟩ := rule_val_tags_nonempty
    exists tag
    apply Finset.mem_of_subset tags_sub_inst_tags
    simp [rule_val_eq] at tag_mem_rule_tags
    exact tag_mem_rule_tags

theorem capture_eq_captureOnTagged_of_ne_untagged
    {n : ℕ}
    {rule : Positive n}
    (rule_val_ne_untagged : rule ≠ Positive.untagged n)
  : capture {rule.val} = captureOnTagged {rule.val} := by
    apply capture_eq_captureOnTagged_of_tags_nonempty
    apply ne_untagged_iff_val_tags_nonempty.mp
    assumption

end Positive

-- TODO: ⚪ Proof this
-- theorem captureOnTagged_positive_eq_captureOnTagged_castSucc
--     {n : ℕ}
--     (rule : Positive n)
--   : ((captureOnTagged {rule.val}) |> Instances.castSucc) = captureOnTagged {rule.val.castSucc} := by
--     sorry

end Rule
