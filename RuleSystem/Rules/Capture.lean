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

end Rule
