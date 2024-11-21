import RuleSystem.Rules.Theorems.Advanced

namespace Instance

def insertLast {n : ℕ} (inst : Instance (n + 1)) : Instance (n + 1)
  := ⟨inst.tags ∪ {Fin.last _}⟩

def insertLastOnCaptureEmbed {n : ℕ} (rule : Rule n) (inst : rule.captureEmbed) : Instance (n + 1)
  := insertLast inst

theorem insertLastOnCaptureEmbed_injective {n : ℕ} (rule : Rule n) : Function.Injective (insertLastOnCaptureEmbed rule) := by
  intro x y insertLast_x_eq_insertLast_y
  ext
  apply eq_iff_tags_eq.mpr
  ext tag
  simp [insertLastOnCaptureEmbed, insertLast] at insertLast_x_eq_insertLast_y
  constructor
  -- TODO: Get rid of the symmetric case
  · intro tag_mem_insertLast_x
    cases Decidable.eq_or_ne tag (Fin.last _) with
      | inl tag_eq_last =>
        have := Instances.val_tags_CastPredPrecondition_of_notContainingLast x tag tag_mem_insertLast_x
        contradiction
      | inr tag_ne_last =>
        have : tag ∈ y.val.tags ∪ {Fin.last _} := by
          have := Finset.mem_union_left {Fin.last _} tag_mem_insertLast_x
          rwa [insertLast_x_eq_insertLast_y] at this
        simp [tag_ne_last] at this
        assumption
  · intro tag_mem_insertLast_y
    cases Decidable.eq_or_ne tag (Fin.last _) with
      | inl tag_eq_last =>
        have := Instances.val_tags_CastPredPrecondition_of_notContainingLast y tag tag_mem_insertLast_y
        contradiction
      | inr tag_ne_last =>
        have : tag ∈ x.val.tags ∪ {Fin.last _} := by
          have := Finset.mem_union_left {Fin.last _} tag_mem_insertLast_y
          rw [← insertLast_x_eq_insertLast_y] at this
          assumption
        simp [tag_ne_last] at this
        assumption

def insertLastOnCaptureEmbedEmbedding {n : ℕ} (rule : Rule n) : rule.captureEmbed ↪ Instance (n + 1)
  := ⟨insertLastOnCaptureEmbed rule, insertLastOnCaptureEmbed_injective rule⟩
end Instance

namespace Rule

def captureEmbedInsertLast {n : ℕ} (rule : Rule n) : Instances (n + 1)
  := rule.captureEmbed.attach.map (Instance.insertLastOnCaptureEmbedEmbedding rule)

end Rule
