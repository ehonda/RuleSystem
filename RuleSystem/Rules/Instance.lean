import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import RuleSystem.Rules.Defs
import RuleSystem.Rules.Fin

-- TODO: Instances for `hasMem` so we can just write `Fin.last _ ∈ inst` (instead of `Fin.last _ ∈ inst.tags`).
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

-- This should be useful fairly often when working with `Instance.castSucc` and `Rule.castSucc`, with regards to their
-- commutativity. Whether or not instances with `last` are captured should often play a crucial role in proofs.
--
-- TODO: ❓ Should we do this or not? Investigate common use cases first.
-- We make `inst` and `inst'` explicit rather than the `of_`-arguments here, because the common use case should be via
-- `apply Instance.false_of_last_mem_of_castSuccEmbedding_eq inst inst'` to then generate sub goals for the
-- `of_`-arguments. Otherwise we would have to resort to the longer and harder to understand
-- `@Instance.false_of_last_mem_of_castSuccEmbedding_eq _ inst inst' _ _`.
theorem false_of_last_mem_of_castSuccEmbedding_eq
    {n : ℕ}
    {inst : Instance n}
    {inst' : Instance (n + 1)}
    (last_mem_inst' : Fin.last _ ∈ inst'.tags)
    (inst_castSuccEmbedding_eq_inst' : inst' = (inst |> castSuccEmbedding))
  : False := by
    simp [inst_castSuccEmbedding_eq_inst', castSuccEmbedding, castSucc] at last_mem_inst'
    obtain ⟨_, _, _⟩ := last_mem_inst'
    apply Fin.false_of_castLE_eq_last
    assumption

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

theorem castPred_castSucc_eq {n : ℕ} {inst : Instance (n + 1)} (h : inst.CastPredPrecondition)
  : (inst.castPred h).castSucc = inst := by
    simp [eq_iff_tags_eq, castSucc, castPred]
    ext tag
    constructor
    · intro tag_mem_castPred_castSucc
      simp [Fin.castSuccEmb, restrictFinCastPred, Subtype.restrict] at tag_mem_castPred_castSucc
      obtain ⟨tag', ⟨_, _, _⟩, _⟩ := tag_mem_castPred_castSucc
      subst tag tag'
      simpa [Fin.castPred, Fin.castLE]
    · intro tag_mem_inst_tags
      simp [Fin.castSuccEmb, restrictFinCastPred, Subtype.restrict]
      have tag_ne_last : tag ≠ Fin.last _ := h tag tag_mem_inst_tags
      set tag' := Fin.castPred tag tag_ne_last with tag'_def
      exists tag'
      constructor
      · exists tag
        exists tag_mem_inst_tags
      · simp [tag'_def, Fin.castPred, Fin.castLE]

theorem castPred_castSuccEmbedding_eq {n : ℕ} {inst : Instance (n + 1)} (h : inst.CastPredPrecondition)
  : (inst.castPred h |> castSuccEmbedding) = inst := by
    simp [castSuccEmbedding, castPred_castSucc_eq]

end Instance

abbrev Instances (n : ℕ) := Finset (Instance n)

namespace Instances

def castSucc {n : ℕ} : Instances n → Instances (n + 1) := Finset.map Instance.castSuccEmbedding

-- TODO: Why can't we write this with the fancy notation?
def containingLast {n : ℕ} : Instances (n + 1) := Finset.univ.filter (λ inst ↦ Fin.last _ ∈ inst.tags)

end Instances
