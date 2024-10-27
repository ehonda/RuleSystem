import RuleSystem.Rules.Theorems.Advanced

namespace Rule

namespace Negative

theorem capture_eq_captureOnTagged
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

end Negative

-- TODO: ⚪ Proof this
-- theorem captureOnTagged_positive_eq_captureOnTagged_castSucc
--     {n : ℕ}
--     (rule : Positive n)
--   : ((captureOnTagged {rule.val}) |> Instances.castSucc) = captureOnTagged {rule.val.castSucc} := by
--     sorry

end Rule
