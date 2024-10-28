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

-- TODO: ⚪ Proof this
theorem captureOnTagged_positive_eq_captureOnTagged_castSucc
    {n : ℕ}
    (rule : Positive n)
  : ((capture {rule.val}) |> Instances.castSucc) = capture {rule.val.castSucc} := by
    ext inst
    obtain ⟨tags, rule_val_eq_positive⟩ := Positive.exists_val_eq_positive rule
    simp [capture, Instances.castSucc, Rule.castSucc, applyTo, appliesTo, rule_val_eq_positive]
    constructor
    · intro exists_inst'
      obtain ⟨inst', tags_subset_inst'_tags, inst'_castSucc_eq_inst⟩ := exists_inst'
      subst inst
      simpa [Instance.castSuccEmbedding, Instance.castSucc]
    · intro castSucc_tags_subset_inst_tags
      -- TODO: Here we basically want `exists inst.castPred h` and we can get h from
      --       `Finset.map Fin.castSuccEmb tags ⊆ inst.tags` (i.e. the fact that `inst` is captured by the
      --       embedding of the positive rule means it can't contain `last`)
      sorry


end Rule
