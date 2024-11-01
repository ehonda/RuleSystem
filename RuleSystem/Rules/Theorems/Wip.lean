import RuleSystem.Rules.Theorems.Advanced

namespace Rule

-- 📜 Open Capture theorems ✅
--
-- We have:
--  * `Negative`
--    * `capture {rule.val} = captureOnTagged {rule.val} ∪ {Instance.untagged}`
--  * `Positive`
--    * `capture {rule.val} ⊆ captureOnTagged {rule.val} ∪ {Instance.untagged}`
--    * (Of `Positive.untagged`): `capture {rule.val} = captureOnTagged {rule.val} ∪ {Instance.untagged}`
--    * (Of `≠ Positive.untagged`): `capture {rule.val} = captureOnTagged {rule.val}`
--
-- What can we prove?
--  * How does `= / ≠ Negative.untagged` affect `capture`?
--    * ❌ It doesn't, as we have shown an equality for `Negative` without any conditions
--  * With `Positive` we have shown the distinction so it doesn't seem like there is anything left

-- 📜 Open castSucc theorems
--
-- * `Negative`
--   * We can show that `last` is captured
-- * `Positive`
--   * See below
--   * ...

end Rule
