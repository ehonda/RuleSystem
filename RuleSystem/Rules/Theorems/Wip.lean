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
-- TODO: Is there a generalized notion of commutativity that applies here? It's not "true" commutativity because we
--       have:
--         * LHS
--           * `f = Instances.castSucc : Instances n → Instances (n + 1)`
--           * `g = Rule.captureFromSingle : Rule n → Instances n`
--         * RHS
--           * `f' = Rule.castSucc : Rule n → Rule (n + 1)`
--           * `g' = Rule.captureFromSingle : Rule (n + 1) → Instances (n + 1)`
--
--       So we have `f ∘ g = g' ∘ f'` instead of `f ∘ g = g ∘ f`, but `f and f'` are related as are `g and g'`.
--
--       🤖 We got a copilot hint suggesting it's a commutative diagram and indeed example 1 here does exactly look
--       like what we need right: https://en.wikipedia.org/wiki/Commutative_diagram#Example_1
--
--       Interpretation: We study the connection between first embedding a rule and then it's captured instances and
--       then the other way around.
--
-- TODO: Fix this proof! See comment marked with ❌
theorem capture_positive_castSucc_comm
    {n : ℕ}
    (rule : Positive n)
  : (capture {rule.val} |> Instances.castSucc) = capture {rule.val.castSucc} := by
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
      have inst_castPredPrecondition : inst.CastPredPrecondition := by
        intro tag tag_mem_inst_tags tag_eq_last
        subst tag
        -- ❌ THIS IS NOT CORRECT! The embedded rule (`rule.val.castSucc`) does still only have tags that are `≠ last`,
        --     but we DO capture instances that contain `last`, e.g. if we have
        --     `universe = {A, B, C}, rule = positive {B}` then we capture `inst = ⟨{B, D}⟩` with the embedded rule
        --
        --     What we should be able to show however is (strict) `subset` on one side and `eq` on the other side. We
        --     can then even show what's missing in the `ssubset` case (the instances that contain `last`).
        sorry
      set inst' := inst.castPred inst_castPredPrecondition with inst'_def
      exists inst'
      simp [inst'_def, Instance.castPred]
      constructor
      · intro tag tag_in_tags
        simp [Instance.restrictFinCastPred, Subtype.restrict]
        set tag' := tag |> Fin.castSucc with tag'_def
        have tag'_in_inst_tags : tag' ∈ inst.tags := by
          apply Finset.mem_of_subset castSucc_tags_subset_inst_tags
          simp [tag'_def]
          exists tag
        exists tag'
        exists tag'_in_inst_tags
      · apply Instance.eq_iff_tags_eq.mpr
        ext tag
        simp [Instance.castSuccEmbedding, Instance.castSucc, Instance.restrictFinCastPred, Subtype.restrict,
          Fin.castPred, Fin.castLT, Fin.castLE]
        constructor
        -- TODO: 🕵️‍♀️ What's going on here? Lots of wheel spinning
        · intro h
          -- TODO: Is there a more elegant way to do this?
          obtain ⟨tag', ⟨_, ⟨_⟩⟩, _⟩ := h
          subst tag tag'
          simpa
        · intro tag_mem_inst_tags
          have tag_ne_last := inst_castPredPrecondition tag tag_mem_inst_tags
          set tag' := tag.castPred tag_ne_last with tag'_def
          exists tag'
          constructor
          · exists tag
            exists tag_mem_inst_tags
          · simp [tag'_def]

end Rule
