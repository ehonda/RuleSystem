import RuleSystem.Rules.Basic

namespace Rule

def capture {n : ℕ} (rules : Rules n) : Finset (Instance n) := {inst | applyTo rules inst}
def captureFromSingle {n : ℕ} (rule : Rule n) := capture {rule}
-- The corresponding subtype
def Capture {n : ℕ} (rules : Rules n) := Subtype (· ∈ capture rules)

instance instDecidableMemCapture {n : ℕ} (rules : Rules n) (inst : Instance n) : Decidable (inst ∈ capture rules)
  := Finset.decidableMem inst (capture rules)

-- TODO: Better name
-- TODO: Can we instead define this with `inst : (Capture rules)`? Then we don't need the `DecidablePred` for
--       `inst ∈ capture rules ∧ inst.tags.Nonempty`
def captureOnTagged {n : ℕ} (rules : Rules n) : Finset (Instance n)
  := {inst | inst ∈ capture rules ∧ inst.tags.Nonempty}
def captureOnTaggedFromSingle {n : ℕ} (rule : Rule n) := captureOnTagged {rule}
-- The corresponding subtype
def CaptureOnTagged {n : ℕ} (rules : Rules n) := Subtype (· ∈ captureOnTagged rules)

-- TODO: Naming
def captureEmbed {n : ℕ} (rule : Rule n) := rule.captureFromSingle |> Instances.castSucc
-- def captureEmbed {n : ℕ} (rule : Rule n) : Finset (@Instances.notContainingLast n)
--   := rule.captureFromSingle |> Instances.castSucc

def embedCapture {n : ℕ} (rule : Rule n) := rule.castSucc.captureFromSingle

instance coeDepCaptureEmbedNotContainingLast {n : ℕ} (rule : Rule n) (inst : rule.captureEmbed)
  : CoeDep rule.captureEmbed inst (@Instances.notContainingLast n) where
    coe := by
      exists inst
      simp [Instances.notContainingLast]
      intro last_mem_inst_tags
      have := inst.property
      simp only [Rule.captureEmbed, Rule.captureFromSingle, Instances.castSucc, Instance.castSuccEmbedding, capture, applyTo, appliesTo] at this
      cases rule_eq : rule <;> (
        simp [rule_eq] at this
        obtain ⟨_, _, inst'_castSucc_eq_inst⟩ := this
        simp [Instance.castSucc, Finset.castSucc, Fin.castSuccEmb, Fin.castAddEmb, Fin.castLEEmb] at inst'_castSucc_eq_inst
        simp [← inst'_castSucc_eq_inst] at last_mem_inst_tags
        obtain ⟨_, _, castLE_eq_last⟩ := last_mem_inst_tags
        exact Fin.false_of_castLE_eq_last castLE_eq_last)

end Rule
