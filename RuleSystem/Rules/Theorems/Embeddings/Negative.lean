import RuleSystem.Rules.Theorems.Advanced

-- TODO: Minimize imports

namespace Rule

namespace Negative

-- TODO: 🔴 Finish this proof
-- 🔮 (EN-0')
theorem captureFromSingle_castSucc_subset_castSucc_captureFromSingle
    {n : ℕ}
    (rule : Negative n)
  : (rule.val.captureFromSingle |> Instances.castSucc) ⊆ rule.val.castSucc.captureFromSingle := by
    sorry

-- 🔮 (EN-0)
theorem captureOnTaggedFromSingle_castSucc_subset_castSucc_captureOnTaggedFromSingle
    {n : ℕ}
    (rule : Negative n)
  : (rule.val.captureOnTaggedFromSingle |> Instances.castSucc) ⊆ rule.val.castSucc.captureOnTaggedFromSingle := by
    obtain ⟨tags, rule_val_eq⟩ := Negative.exists_val_eq_negative rule
    simp [captureOnTaggedFromSingle, captureOnTagged, rule_val_eq, Instances.castSucc, Instance.castSucc, Instance.castSuccEmbedding]
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

-- 🔮 (EN-1)
theorem captureOnTagged_negative_ssub_captureOnTagged_castSucc
    {n : ℕ}
    (rule : Negative n)
  : (rule.val.captureOnTaggedFromSingle |> Instances.castSucc) ⊂ rule.val.castSucc.captureOnTaggedFromSingle := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · apply captureOnTaggedFromSingle_castSucc_subset_castSucc_captureOnTaggedFromSingle
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
      simp [captureOnTaggedFromSingle] at h
      rw [h] at this
      contradiction

end Negative

end Rule
