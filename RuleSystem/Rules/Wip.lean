import RuleSystem.Rules.Theorems.Advanced

namespace Instance

def insertLast {n : ℕ} (inst : Instance (n + 1)) : Instance (n + 1)
  := ⟨inst.tags ∪ {Fin.last _}⟩

-- TODO: Can we use `insertLast` instead?
def insertLast'' {n : ℕ} (rule : Rule n) (inst : rule.captureEmbed) : Instance (n + 1)
  := ⟨inst.val.tags ∪ {Fin.last _}⟩

-- TODO: Finish proof
theorem insertLast''_injective {n : ℕ} (rule : Rule n) : Function.Injective (insertLast'' rule) := by
  sorry

def insertLast''Embedding {n : ℕ} (rule : Rule n) : rule.captureEmbed ↪ Instance (n + 1)
  := ⟨insertLast'' rule, insertLast''_injective rule⟩
end Instance

namespace Rule

def captureEmbedInsertLast {n : ℕ} (rule : Rule n) : Instances (n + 1)
  := rule.captureEmbed.attach.map (Instance.insertLast''Embedding rule)

-- def captureEmbedEmbedding

-- instance {n : ℕ} (rule : Rule n) : CoeDep (Instances (n + 1)) rule.captureEmbed (Finset (@Instances.notContainingLast n)) where
--   coe := by
--     exists rule.captureEmbed.map (Subtype (· ∈ @Instances.notContainingLast n))

--     sorry


-- TODO: Finish this 🍊
-- (Instances.insertLast' rule.val.captureEmbed)
-- application type mismatch
--   Instances.insertLast' (↑rule).captureEmbed
-- argument
--   (↑rule).captureEmbed
-- has type
--   Instances (n + 1) : Type
-- but is expected to have type
--   Finset { x // x ∈ Instances.notContainingLast } : Type

-- This is probably wrong / not what we want
-- instance CoeDepCaptureEmbedNotContainingLast {n : ℕ} (rule : Rule n) (x : Instances (n + 1)) (h : x = rule.captureEmbed)
--   : CoeDep (Instances (n + 1)) x (Finset (@Instances.notContainingLast n)) where
--     coe := by
--       exists x.val

--       -- exists rule.captureEmbed
--       sorry

end Rule