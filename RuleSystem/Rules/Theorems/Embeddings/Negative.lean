import RuleSystem.Rules.Theorems.Advanced

-- TODO: Minimize imports

namespace Rule

namespace Negative

-- 🔮 (EN-0)
theorem captureFromSingle_castSucc_subset_castSucc_captureFromSingle
    {n : ℕ}
    {rule : Negative n}
  : (rule.val.captureFromSingle |> Instances.castSucc) ⊆ rule.val.castSucc.captureFromSingle := by
    intro inst inst_mem_capture_castSucc
    obtain ⟨_, rule_val_eq_negative⟩ := Negative.exists_val_eq_negative rule
    simp [captureFromSingle, capture, Instances.castSucc, Rule.castSucc, applyTo, appliesTo, rule_val_eq_negative] at *
    obtain ⟨_, _, _⟩
      := inst_mem_capture_castSucc
    subst inst
    simp [Instance.castSuccEmbedding, Instance.castSucc]
    apply Finset.inter_eq_empty_iff_inter_map_castSuccEmb_eq_empty.mp
    assumption

-- TODO: Adjust text for the proof idea, it's not quite accurate
-- 🔮 (EN-1)
-- Proof idea is as follows: We show that there is an instance captured by the embedded rule that is not captured by
-- embedding the rule captures. To see why this is true, consider the following example:
--
--  * `universe = {A, B, C}, rule = negative {B}`
--  * `inst = ⟨{A, D}⟩`
--
-- We can capture `inst` with the embedded rule, since `{B} ∩ {A, D} = ∅`, but we can't get `{A, D}` from embedding any
-- of the captures of the original rule, as `{D}` is the last element of the universe embedded into, which we can't get
-- via `castSucc`.
-- Note that it works for the untagged rule as well, where we can just use `inst = ({D})` in the above example.
theorem captureFromSingle_castSucc_ssubset_castSucc_captureFromSingle
    {n : ℕ}
    {rule : Negative n}
  : (rule.val.captureFromSingle |> Instances.castSucc) ⊂ rule.val.castSucc.captureFromSingle := by
    apply (Finset.ssubset_iff_of_subset captureFromSingle_castSucc_subset_castSucc_captureFromSingle).mpr
    obtain ⟨_, rule_val_eq_negative⟩ := Negative.exists_val_eq_negative rule
    simp [captureFromSingle, capture, Instances.castSucc, Rule.castSucc, applyTo, appliesTo, rule_val_eq_negative] at *
    set inst := Instance.mk {Fin.last n} with inst_def
    exists inst
    constructor
    · simp [inst_def]
      apply Finset.inter_singleton_of_not_mem
      simp [Fin.castSuccEmb]
      intro _ _ _
      apply Fin.false_of_castLE_eq_last
      assumption
    · intro _ _
      intro inst'_castSuccEmbedding_eq_inst
      have last_mem_inst_tags : Fin.last _ ∈ inst.tags := by simp [inst_def]
      exact Instance.false_of_last_mem_of_castSuccEmbedding_eq last_mem_inst_tags inst'_castSuccEmbedding_eq_inst.symm

end Negative

end Rule
