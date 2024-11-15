import RuleSystem.Rules.Theorems.Embeddings.Positive
import RuleSystem.Rules.Wip

-- TODO: Minimize imports

namespace Rule

namespace Positive

-- 🔮 (EP-3)
-- TODO: Naming
-- TODO: Fix the theorem statement, what we want to do is basically
--          `captureEmbed ∪ captureEmbed.insertLast = embedCapture`
-- TODO: Use `Finset.disjUnion` here
theorem ep_3
    {n : ℕ}
    {rule : Positive n}
  : rule.val.captureEmbed ∪ (Instances.insertLast' rule.val.captureEmbed) = rule.val.embedCapture := by
    sorry

end Positive

end Rule
