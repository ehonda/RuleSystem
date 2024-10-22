import RuleSystem.Rules.Capture
import RuleSystem.Rules.Transformation
import RuleSystem.Rules.Theorems.Basic

namespace Rule

-- TODO: Show stuff like `captureOnTagged (positive {t, s}) ⊆ captureOnTagged {positive {t}, positive {s}}` etc.
-- TODO: Maybe also show when the are equal

theorem captureOnTagged_positive_sub_captureOnTagged_split
    {n : ℕ}
    (rule : Positive n)
    (rule_val_tags_nonempty : rule.val.tags.Nonempty)
  : captureOnTagged {rule.val} ⊆ captureOnTagged (split rule) := by
    obtain ⟨tags, rule_val_eq⟩ := Positive.exists_val_eq_positive rule
    simp [captureOnTagged, split]
    intro inst inst_mem_captureOnTagged
    simp [capture, applyTo, appliesTo, rule.property, rule_val_eq] at inst_mem_captureOnTagged
    simp [capture, applyTo, appliesTo, Positive.fromTagEmbedding, Positive.fromTag, Positive.fromTags, rule_val_eq]
    constructor
    · obtain ⟨tag, tag_mem_rule_tags⟩ := rule_val_tags_nonempty
      simp [rule_val_eq, Rule.tags] at tag_mem_rule_tags
      exists tag
      constructor
      · assumption
      · exact Finset.mem_of_subset inst_mem_captureOnTagged.left tag_mem_rule_tags
    · exact inst_mem_captureOnTagged.right

-- TODO: Better name
-- theorem captureOnTagged_positive_sub_captureOnTagged_split

-- What we can show is that for negative rules, we have a correspondence on the (tagged) capture between the rule and
-- its positive counterparts, by virtue of the positive rules capturing at least the same instances as the negative
-- rule. Example:
--
-- Tag Universe: {A, B, C, D, E}
-- Negative Rule: N {C}
-- Positive Rules: [P0 {A}, P1 {B}, P2 {D}, P3 {E}]
-- Instances: I0 {A}, I1 {C, D}, I2 {B}
--
-- We then have:
--    appliesTo (N {C}) (I0 {A}) = True (Since {C} ∩ {A} = ∅)
--    appliesTo (N {C}) (I1 {C, D}) = False (Since {C} ∩ {C, D} = {C} ≠ ∅)
--    appliesTo (N {C}) (I2 {B}) = True (Since {C} ∩ {B} = ∅)
--    -> Capture {N {C}} = [I0 {A}, I2 {B}]
--
-- While for the positive rules:
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I0 {A}) = appliesTo (P0 {A}) (I0 {A}) = True (Since {A} ⊆ {A})
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I1 {C, D}) = appliesTo (P2 {D}) (I1 {C, D}) = True (Since {D} ⊆ {C, D})
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I2 {B}) = appliesTo (P1 {B}) (I2 {B}) = True (Since {B} ⊆ {B})
--    -> Capture [P0 {A}, P1 {B}, P2 {D}, P3 {E}] = [I0 {A}, I1 {C, D}, I2 {B}] ⊇ [I0 {A}, I2 {B}] = Capture {N {C}}
--
-- Proof idea is as follows:
--    (I) We take an `inst` in the tagged capture (i.e. `inst.tags` is nonempty) of the negative rule.
--    (II) We show that there exists a rule in the positive counterparts that captures the same `inst`.
--      (a) `inst` is covered by a positive counterpart if we can find a tag in `inst.tags` for which such a positive
--          counterpart rule exists.
--      (b) We get that from the fact that `inst` tags are nonempty (tagged capture), so we have at least one `tag'` in
--          `inst.tags` (that must also be different from the negative rule tag, since `inst` is captured by the
--          negative rule).
--      (c) Since `tag'` is different from the `tag` used by the negative rule, there exists a positive counterpart rule
--          with that `tag'`, capturing `inst`.
--
-- Note that the "onTagged"-Restriction is necessary, since e.g. `I {}` would be captured by any negative rule, but no
-- positive counterpart can capture it since it has no tags, and all of our positive counterparts have at exactly one
-- tag (We would need a tag-less positive rule to capture it).
-- We prove the stronger `captureOnTagged negative ⊆ captureOnTagged positives` here (from which we also have
-- `captureOnTagged negative ⊆ capture positives`, as `captureOnTagged positives ⊆ capture positives`).
theorem captureOnTagged_singleton_negative_sub_captureOnTagged_toPositives {n : ℕ} (rule : Negative n)
  : captureOnTagged {rule.val} ⊆ captureOnTagged (Negative.toPositives rule) := by
      obtain ⟨tags, rule_val_eq⟩ := Negative.exists_val_eq_negative rule
      simp [capture, captureOnTagged, Negative.toPositives, applyTo]
      intro inst inst_mem_captureOnTagged
      simp [rule.property] at inst_mem_captureOnTagged
      simp [rule_val_eq] at *
      constructor
      · obtain ⟨tag, tag_mem_inst_tags⟩ := inst_mem_captureOnTagged.right
        exists tag
        constructor
        · intro tag_mem_rule_tags
          have tag_mem_inter : tag ∈ tags ∩ inst.tags := Finset.mem_inter_of_mem tag_mem_rule_tags tag_mem_inst_tags
          have inter_eq_empty : tags ∩ inst.tags = ∅ := inst_mem_captureOnTagged.left
          simp [inter_eq_empty] at tag_mem_inter
        · rw [@Positive.appliesTo_fromTagEmbedding n tag inst]
          simpa
      · exact inst_mem_captureOnTagged.right

end Rule
