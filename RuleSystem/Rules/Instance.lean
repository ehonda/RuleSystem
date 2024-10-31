import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import RuleSystem.Rules.Defs

structure Instance (n : ℕ) where
  tags : Tags n

namespace Instance

def untagged {n : ℕ} : Instance n := ⟨∅⟩

def tagsEmbedding {n : ℕ} : Tags n ↪ Instance n := ⟨Instance.mk, by simp [Function.Injective]⟩

instance fintype {n : ℕ} : Fintype (Instance n) :=
  let tagsUniv : Tags n := Finset.univ
  let tagsPowerset := tagsUniv.powerset
  let elems := tagsPowerset.map tagsEmbedding

  let complete : ∀ inst : Instance n, inst ∈ elems := by
    simp [Instance, elems, tagsEmbedding, tagsPowerset, tagsUniv]

  ⟨elems, complete⟩

theorem eq_iff_tags_eq {n : ℕ} {inst inst' : Instance n} : inst = inst' ↔ inst.tags = inst'.tags := by
  cases inst; cases inst'; simp

theorem eq_mk_iff_tags_eq {n : ℕ} {tags : Tags n} {inst : Instance n}
  : inst = ⟨tags⟩ ↔ inst.tags = tags := eq_iff_tags_eq

instance instDecidableEq {n : ℕ} : DecidableEq (Instance n)
  := λ _ _ ↦ decidable_of_iff' _ eq_iff_tags_eq

instance instDecidableTagsNonempty {n : ℕ} (inst : Instance n) : Decidable (inst.tags.Nonempty)
  := Finset.decidableNonempty

def castSucc {n : ℕ} (inst : Instance n) : Instance (n + 1) := ⟨inst.tags.map Fin.castSuccEmb⟩

def castSuccEmbedding {n : ℕ} : Instance n ↪ Instance (n + 1) :=
  ⟨castSucc, by simp [Function.Injective, castSucc, eq_iff_tags_eq]⟩

-- TODO: 🕵️‍♀️ Revisit! The whole block about `castPred` is just copied from `TheoremsAboutAlgorithms` and works, but we
--        should wrap our head around it once more. See:
--          * https://github.com/ehonda/TheoremsAboutAlgorithms/blob/a8d8a946f0e34dd987996f1f7f209bf61a598a72/TheoremsAboutAlgorithms/Partitions/WithFinset/Cell.lean#L122-L123

def CastPredPrecondition {n : ℕ} (inst : Instance (n + 1)) := ∀ tag ∈ inst.tags, tag ≠ Fin.last _

-- We're using `Subtype.restrict` here. Revisit this to fully understand what's going on here.
def restrictFinCastPred {n : ℕ} (inst : Instance (n + 1)) (h : inst.CastPredPrecondition) (tag : inst.tags) : Fin n
  := tag.restrict (· ∈ inst.tags) Fin.castPred (h tag tag.property)

theorem restrictFinCastPred_injective {n : ℕ} (inst : Instance (n + 1)) (h : inst.CastPredPrecondition)
  : Function.Injective (restrictFinCastPred inst h) := by
    intro x y castPred_x_eq_castPred_y
    simp [restrictFinCastPred] at castPred_x_eq_castPred_y
    apply Subtype.eq
    exact Fin.castPred_inj.mp castPred_x_eq_castPred_y

def castPred {n : ℕ} (inst : Instance (n + 1)) (h : inst.CastPredPrecondition) : Instance n :=
  ⟨Finset.univ.map ⟨inst.restrictFinCastPred h, restrictFinCastPred_injective inst h⟩⟩

end Instance

abbrev Instances (n : ℕ) := Finset (Instance n)

namespace Instances

def castSucc {n : ℕ} : Instances n → Instances (n + 1) := Finset.map Instance.castSuccEmbedding

end Instances
