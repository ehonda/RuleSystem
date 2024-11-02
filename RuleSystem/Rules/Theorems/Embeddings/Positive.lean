import RuleSystem.Rules.Theorems.Advanced

-- TODO: Minimize imports

namespace Rule

namespace Positive

-- 🔮 (EP-0)
-- The naming here follows the (pseudo) dot notation: `rule.capture.castSucc ⊆ rule.castSucc.capture`
theorem captureFromSingle_castSucc_subset_castSucc_captureFromSingle
    {n : ℕ}
    {rule : Positive n}
  : (rule.val.captureFromSingle |> Instances.castSucc) ⊆ rule.val.castSucc.captureFromSingle := by
    intro inst inst_mem_capture_castSucc
    obtain ⟨_, rule_val_eq_positive⟩ := Positive.exists_val_eq_positive rule
    simp [captureFromSingle, capture, Instances.castSucc, Rule.castSucc, applyTo, appliesTo, rule_val_eq_positive] at *
    obtain ⟨_, _, _⟩ := inst_mem_capture_castSucc
    subst inst
    simpa [Instance.castSuccEmbedding, Instance.castSucc]

-- 🔮 (EP-1)
-- Proof idea is as follows: We show that there is an instance captured by the embedded rule that is not captured by
-- embedding the rule captures. To see why this is true, consider the following example:
--
--  * `universe = {A, B, C}, rule = positive {B}`
--  * `inst = ⟨{B, D}⟩`
--
-- We can capture `inst` with the embedded rule, since `{B} ⊆ {B, D}`, but we can't get `{B, D}` from embedding any of
-- the captures of the original rule, as `{D}` is the last element of the universe embedded into, which we can't get via
-- `castSucc`.
-- Note that it works for the untagged rule as well, where we can just use `inst = ({D})` in the above example.
theorem captureFromSingle_castSucc_ssubset_castSucc_captureFromSingle
    {n : ℕ}
    {rule : Positive n}
  : (rule.val.captureFromSingle |> Instances.castSucc) ⊂ rule.val.castSucc.captureFromSingle := by
    apply (Finset.ssubset_iff_of_subset captureFromSingle_castSucc_subset_castSucc_captureFromSingle).mpr
    obtain ⟨tags, rule_val_eq_positive⟩ := Positive.exists_val_eq_positive rule
    simp [captureFromSingle, capture, Instances.castSucc, Rule.castSucc, applyTo, appliesTo, rule_val_eq_positive]
    set inst := Instance.mk (tags.map Fin.castSuccEmb ∪ {Fin.last _}) with inst_def
    exists inst
    constructor
    · simp [inst_def, Finset.subset_union_left]
    · intro inst' _ inst'_castSuccEmbedding_eq_inst
      apply @Instance.false_of_last_mem_of_castSuccEmbedding_eq _ inst' inst _ _
      · simp [inst_def]
      · symm; assumption

-- 🔮 (EP-2)
-- Here we explicitly show what's missing from the embedding of the capture of the original rule to the capture of the
-- embedded rule.
theorem captureFromSingle_castSucc_eq_castSucc_captureFromSingle_sdiff_containingLast
    {n : ℕ}
    {rule : Positive n}
  : (rule.val.captureFromSingle |> Instances.castSucc) = rule.val.castSucc.captureFromSingle \ Instances.containingLast := by
    ext inst
    obtain ⟨tags, rule_val_eq_positive⟩ := Positive.exists_val_eq_positive rule
    constructor
    · intro inst_mem_captureFromSingle_castSucc
      have inst_mem_castSucc_captureFromSingle
        := captureFromSingle_castSucc_subset_castSucc_captureFromSingle inst_mem_captureFromSingle_castSucc
      simp [inst_mem_castSucc_captureFromSingle, Instances.containingLast]
      intro last_mem_inst_tags
      simp [Instances.castSucc, captureFromSingle, rule_val_eq_positive, capture, applyTo, appliesTo]
        at inst_mem_captureFromSingle_castSucc
      obtain ⟨_, _, inst'_castSuccEmbedding_eq_inst⟩ := inst_mem_captureFromSingle_castSucc
      exact Instance.false_of_last_mem_of_castSuccEmbedding_eq last_mem_inst_tags inst'_castSuccEmbedding_eq_inst.symm
    · intro inst_mem_castSucc_captureFromSingle_sub_containingLast
      simp [
        Instances.castSucc, Rule.castSucc, captureFromSingle, rule_val_eq_positive, capture, applyTo, appliesTo,
        Instances.containingLast] at *
      have inst_castPredPrecondition : inst.CastPredPrecondition := by
        intro _ tag_mem_inst_tags tag_eq_last
        simp [tag_eq_last] at tag_mem_inst_tags
        obtain ⟨_, _⟩ := inst_mem_castSucc_captureFromSingle_sub_containingLast
        contradiction
      set inst' := inst.castPred inst_castPredPrecondition with inst'_def
      exists inst'
      constructor
      · intro tag tag_mem_inst_tags
        simp [inst'_def, Instance.castPred, Instance.restrictFinCastPred, Subtype.restrict]
        set tag' := tag |> Fin.castSucc with tag'_def
        exists tag'
        simp [tag'_def]
        apply Finset.mem_of_subset inst_mem_castSucc_captureFromSingle_sub_containingLast.left
        simp
        exists tag
      · simp [inst'_def]
        apply Instance.castPred_castSuccEmbedding_eq

end Positive

end Rule
