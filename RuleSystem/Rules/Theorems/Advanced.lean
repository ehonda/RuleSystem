import RuleSystem.Rules.Capture
import RuleSystem.Rules.Transformation
import RuleSystem.Rules.Theorems.Basic

namespace Rule

-- TODO: Show stuff like `captureOnTagged (positive {t, s}) ⊆ captureOnTagged {positive {t}, positive {s}}` etc.
-- TODO: Maybe also show when they are equal

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

theorem captureOnTagged_negative_sub_captureOnTagged_split
    {n : ℕ}
    (rule : Negative n)
    (rule_val_tags_nonempty : rule.val.tags.Nonempty)
  : captureOnTagged {rule.val} ⊆ captureOnTagged (split rule) := by
    obtain ⟨tags, rule_val_eq⟩ := Negative.exists_val_eq_negative rule
    simp [captureOnTagged, split]
    intro inst inst_mem_captureOnTagged
    simp [capture, applyTo, appliesTo, rule.property, rule_val_eq] at inst_mem_captureOnTagged
    simp [capture, applyTo, appliesTo, Negative.fromTagEmbedding, Negative.fromTag, Negative.fromTags, rule_val_eq]
    constructor
    · obtain ⟨tag, tag_mem_rule_tags⟩ := rule_val_tags_nonempty
      simp [rule_val_eq, Rule.tags] at tag_mem_rule_tags
      exists tag
      constructor
      · assumption
      · have : {tag} ⊆ tags := Finset.singleton_subset_iff.mpr tag_mem_rule_tags
        have : {tag} ∩ inst.tags ⊆ tags ∩ inst.tags := Finset.inter_subset_inter_right this
        rw [inst_mem_captureOnTagged.left] at this
        exact Finset.subset_empty.mp this
    · exact inst_mem_captureOnTagged.right

theorem captureOnTagged_negative_sub_captureOnTagged_castSucc
    {n : ℕ}
    (rule : Negative n)
  : ((captureOnTagged {rule.val}) |> Instances.castSucc) ⊆ captureOnTagged {rule.val.castSucc} := by
    obtain ⟨tags, rule_val_eq⟩ := Negative.exists_val_eq_negative rule
    simp [captureOnTagged, rule_val_eq, Instances.castSucc, Instance.castSucc, Instance.castSuccEmbedding]
    intro inst inst_mem_captureOnTagged
    simp [capture, applyTo, appliesTo, rule.property] at inst_mem_captureOnTagged
    obtain ⟨inst', ⟨tags_inter_inst'_tags_eq_empty, inst'_tags_nonempty⟩, inst'_castSucc_eq_inst⟩
      := inst_mem_captureOnTagged
    simp [capture, applyTo, appliesTo, Rule.castSucc]
    constructor
    · apply Finset.eq_empty_of_forall_not_mem
      intro tag tag_mem_inter
      simp at tag_mem_inter
      obtain ⟨⟨tag', tag'_mem_tags, tag'_castLE_eq_tag⟩, tag_mem_inst_tags⟩ := tag_mem_inter
      have : tag' ∈ (tags ∩ inst'.tags) := by
        simp
        constructor
        · assumption
        · rw [← tag'_castLE_eq_tag, ← inst'_castSucc_eq_inst] at tag_mem_inst_tags
          simp [Fin.castLE, Instance.castSucc] at tag_mem_inst_tags
          obtain ⟨tag'', _, tag''_eq_tag'⟩ := tag_mem_inst_tags
          have := Fin.val_inj.mp tag''_eq_tag'
          subst tag''
          assumption
      rw [tags_inter_inst'_tags_eq_empty] at this
      contradiction
    · obtain ⟨tag', _⟩ := inst'_tags_nonempty
      set tag := Fin.castSucc tag' with tag_def
      exists tag
      rw [← inst'_castSucc_eq_inst]
      simp [tag_def, Instance.castSucc]
      exists tag'

theorem captureOnTagged_negative_ssub_captureOnTagged_castSucc
    {n : ℕ}
    (rule : Negative n)
  : ((captureOnTagged {rule.val}) |> Instances.castSucc) ⊂ captureOnTagged {rule.val.castSucc} := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · apply captureOnTagged_negative_sub_captureOnTagged_castSucc
    · simp
      intro h
      obtain ⟨tags, rule_val_eq⟩ := Negative.exists_val_eq_negative rule
      -- TODO: These look pretty similar, maybe we can unify them
      have : ⟨{Fin.last _}⟩ ∈ captureOnTagged {rule.val.castSucc} := by
        simp [captureOnTagged, Rule.castSucc, rule_val_eq, capture, applyTo, appliesTo]
        apply Finset.inter_singleton_of_not_mem
        simp [Fin.castSuccEmb, Fin.castLE]
        -- TODO: There should be a simpler way to do this
        intro tag _
        intro tag_val_eq_last
        apply Fin.val_eq_of_eq at tag_val_eq_last
        simp at tag_val_eq_last
        have : ↑tag ≠ n := Nat.ne_of_lt tag.isLt
        contradiction
      have : ⟨{Fin.last _}⟩ ∉ ((captureOnTagged {rule.val}) |> Instances.castSucc) := by
        simp [captureOnTagged, Instances.castSucc, capture, rule_val_eq, applyTo, appliesTo, Instance.castSuccEmbedding]
        intro inst _ _
        simp [Instance.castSucc]
        intro castSucc_inst_tags_eq_singleton_last
        have : Fin.last _ ∈ Finset.map Fin.castSuccEmb inst.tags := by
          rw [castSucc_inst_tags_eq_singleton_last]
          simp
        simp [Fin.castLE] at this
        obtain ⟨tag, _, tag_eq_last⟩ := this
        apply Fin.val_eq_of_eq at tag_eq_last
        simp at tag_eq_last
        have : ↑tag ≠ n := Nat.ne_of_lt tag.isLt
        contradiction
      rw [h] at this
      contradiction

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

end Rule
