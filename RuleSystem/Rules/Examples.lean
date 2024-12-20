import RuleSystem.Rules.Basic
import RuleSystem.Rules.Transformation

open Rule

-- def rule := @Positive.fromTag 3 0
-- def rule := @Positive.fromTag 3 1
def rule : Rule 3 := (Negative.fromTag 0).val
def inst : Instance 3 := ⟨{0}⟩

#eval @appliesTo 3 rule inst

-- Some examples. An easier mental model to think about these could be to use the example setup from `Defs.lean`, i.e.
-- the instances represent servers and we have the following correspondence for our tags:
--
--    `{0, 1, 2, 3}` ➡ `{LOCATION_DE, LOCATION_US, GAME_WOW, GAME_DOTA2}`
--
-- Then the following rules could be interpreted as:
--
--    - `Rule.positive {0}`: "This rule applies to all servers in Germany (irrespective of which games they run)."
--    - `Rule.negative {1}`: "This rule applies to all servers that are not in the US (irrespective of which games they
--                            run, or if they run any games at all)."
--    - `Rule.positive {0, 2}`: "This rule applies to all servers in Germany running World of Warcraft. Note that this
--                               rule also applies if a server is additionally running Dota 2."

example : @appliesTo 1 (Rule.positive {0}) ⟨{0}⟩ := by
  simp only [appliesTo, Finset.Subset.refl]

example : @appliesTo 3 (Rule.negative {1}) ⟨{0}⟩ := by
  simp only [appliesTo]
  decide

-- example : @appliesTo 3 (Rule.negative {1}) ⟨{3, 4}⟩ := by
--   simp only [appliesTo]
--   apply Finset.singleton_inter_of_not_mem
--   -- TODO: How do we best prove `1 ∉ {3, 4}`?

example : @appliesTo 3 (Rule.positive {0, 2}) ⟨{0, 2, 3}⟩ := by
  simp [appliesTo]
  decide
