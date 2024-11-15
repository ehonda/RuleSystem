import RuleSystem.Rules.Theorems.Advanced

namespace Rule


-- TODO: Finish this 🍊
-- application type mismatch
--   Instances.insertLast' (↑rule).captureEmbed
-- argument
--   (↑rule).captureEmbed
-- has type
--   Instances (n + 1) : Type
-- but is expected to have type
--   Finset { x // x ∈ Instances.notContainingLast } : Type

-- This is probably wrong / not what we want
-- instance CoeDepCaptureEmbedNotContainingLast {n : ℕ} (rule : Rule n)
--   : CoeDep (Instances (n + 1)) rule.captureEmbed (Finset (@Instances.notContainingLast n)) where
--     coe := by
--       -- exists rule.captureEmbed
--       sorry

end Rule
