import RuleSystem.Rules.Theorems.Embeddings.Positive

-- TODO: Minimize imports

namespace Rule

namespace Positive

-- TODO: These defs should be somewhere else

-- TODO: Naming
def captureEmbed {n : ℕ} (rule : Positive n) := rule.val.captureFromSingle |> Instances.castSucc

-- TODO: Move to Instances.lean
-- TODO: Naming
def insertLast' {n : ℕ} (inst : Instance (n + 1)) : Instance (n + 1) := ⟨inst.tags ∪ {Fin.last _}⟩

-- TODO: Fix these, move them to the correct place
-- def insertLast'_embedding {n : ℕ} : Finset (Instance (n + 1)) ↪ Finset (Instance (n + 1)) :=
--   ⟨insertLast', by simp [Function.Injective, insertLast']⟩

-- def insertLast {n : ℕ} (instances : Instances n) := instances.map insertLast'_embedding

-- 🔮 (EP-3)
-- TODO: Naming
-- TODO: Fix the theorem statement, what we want to do is basically
--          `captureEmbed ∪ captureEmbed.insertLast = embedCapture`
theorem ep_3
    {n : ℕ}
    {rule : Positive n}
  : (rule.val.captureFromSingle |> Instances.castSucc) = rule.val.castSucc.captureFromSingle := by
    sorry

end Positive

end Rule
