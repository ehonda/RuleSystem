import RuleSystem.Rules.Defs
import RuleSystem.Rules.Instance

inductive Rule (n : ℕ) where
  | positive (tags : Tags n)
  | negative (tags : Tags n)

namespace Rule

-- TODO: Should this be inside the `Rule` namespace or not?
abbrev Rules (n : ℕ) := Finset (Rule n)

def tags {n : ℕ} (rule : Rule n) : Tags n :=
  match rule with
  | .positive tags => tags
  | .negative tags => tags

def appliesTo {n : ℕ} (rule : Rule n) (inst : Instance n) : Prop :=
  match rule with
  | .positive tags => tags ⊆ inst.tags
  | .negative tags => tags ∩ inst.tags = ∅

def applyTo {n : ℕ} (rules : Rules n) (inst : Instance n) : Prop :=
  ∃ rule ∈ rules, (appliesTo · inst) rule

-- TODO: Use type class inference to construct some of this, i.e. `inferInstance` and the like
instance instDecidableAppliesTo {n : ℕ} (rule : Rule n) (inst : Instance n) : Decidable (appliesTo rule inst)
  := match rule with
    | .positive tags => Finset.instDecidableRelSubset tags inst.tags
    | .negative tags => match @Finset.decidableNonempty _ (tags ∩ inst.tags) with
      | isTrue h => isFalse (Finset.Nonempty.ne_empty h)
      | isFalse h => isTrue (Finset.not_nonempty_iff_eq_empty.mp h)

-- TODO: This looks like a prime candidate for type class inference (if used correctly?)
instance instDecidableApplyTo {n : ℕ} (rules : Rules n) (inst : Instance n) : Decidable (applyTo rules inst) :=
  match @Finset.decidableExistsAndFinset _ rules (appliesTo · inst) _ with
    | isTrue h => isTrue h
    | isFalse h => isFalse h

def castSucc {n : ℕ} (rule : Rule n) : Rule (n + 1) :=
  match rule with
  | .positive tags => .positive (tags.map Fin.castSuccEmb)
  | .negative tags => .negative (tags.map Fin.castSuccEmb)

def castSuccEmbedding {n : ℕ} : Rule n ↪ Rule (n + 1) :=
  let castSucc_inj : castSucc.Injective := by
    simp [Function.Injective, castSucc]
    intro rule rule' castSucc_eq
    cases h : rule <;> cases h' : rule' <;> simp [h, h'] at castSucc_eq <;> simp [castSucc_eq]
  ⟨castSucc, castSucc_inj⟩

end Rule
