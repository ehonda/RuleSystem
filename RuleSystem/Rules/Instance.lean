import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import RuleSystem.Rules.Defs

structure Instance (n : ℕ) where
  (tags : Tags n)

namespace Instance

def mkEmbedding {n : ℕ} : Tags n ↪ Instance n := ⟨Instance.mk, by simp [Function.Injective]⟩

instance fintype {n : ℕ} : Fintype (Instance n) :=
  let tagsUniv : Tags n := Finset.univ
  let tagsPowerset := tagsUniv.powerset
  let elems := tagsPowerset.map mkEmbedding

  let complete : ∀ inst : Instance n, inst ∈ elems := by
    simp [Instance, elems, mkEmbedding, tagsPowerset, tagsUniv]

  ⟨elems, complete⟩

end Instance
