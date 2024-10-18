import RuleSystem.Rules.Defs
import RuleSystem.Rules.Finset
import RuleSystem.Rules.Instance
import RuleSystem.Rules.Tags
import Mathlib.Data.Fintype.Basic

-- TODO: Cleanup file structure

inductive Rule (n : ℕ) where
  | positive (tags : Tags n)
  | negative (tags : Tags n)

namespace Rule

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

def IsPositive {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => True
  | .negative _ => False

def Positive (n : ℕ) := Subtype (@IsPositive n)

namespace Positive

def fromTags {n : ℕ} (tags : Tags n) : Positive n := ⟨Rule.positive tags, by simp only [Rule.IsPositive]⟩

def fromTagsEmbedding {n : ℕ} : Tags n ↪ Positive n :=
  let fromTags_inj : fromTags.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [fromTags, positive.injEq] at this
    assumption
  ⟨fromTags, fromTags_inj⟩

end Positive

-- TODO: Why is this not found if we don't explicitly define it here? I.e. the theorem below does not type check without
--       this
instance instCoeOutPositiveRules {n : ℕ} : CoeOut (Finset (Positive n)) (Rules n) := Finset.instCoeOutSubtype

def IsNegative {n : ℕ} (rule : Rule n) : Prop :=
  match rule with
  | .positive _ => False
  | .negative _ => True

def Negative (n : ℕ) := Subtype (@IsNegative n)

namespace Negative

def fromTags {n : ℕ} (tags : Tags n) : Negative n := ⟨Rule.negative tags, by simp only [Rule.IsNegative]⟩

def fromTagsEmbedding {n : ℕ} : Tags n ↪ Negative n :=
  let fromTags_inj : fromTags.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [fromTags, negative.injEq] at this
    assumption
  ⟨fromTags, fromTags_inj⟩

end Negative

-- TODO: Why is this not found if we don't explicitly define it here?
instance instCoeOutNegativeRules {n : ℕ} : CoeOut (Finset (Negative n)) (Rules n) := Finset.instCoeOutSubtype

theorem false_of_isPositive_of_isNegative
    {n : ℕ}
    {rule : Rule n}
    (h_pos : IsPositive rule)
    (h_neg : IsNegative rule)
  : False := by cases rule with
    | positive => exact h_neg
    | negative => exact h_pos

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

def capture {n : ℕ} (rules : Rules n) : Finset (Instance n) := {inst | applyTo rules inst}
-- The corresponding subtype
def Capture {n : ℕ} (rules : Rules n) := Subtype (· ∈ capture rules)

instance instDecidableTagsNonempty {n : ℕ} (inst : Instance n) : Decidable (inst.tags.Nonempty)
  := Finset.decidableNonempty

instance instDecidableMemCapture {n : ℕ} (rules : Rules n) (inst : Instance n) : Decidable (inst ∈ capture rules)
  := Finset.decidableMem inst (capture rules)

-- TODO: Better name
-- TODO: Can we instead define this with `inst : (Capture rules)`? Then we don't need the `DecidablePred` for
--       `inst ∈ capture rules ∧ inst.tags.Nonempty`
def captureOnTagged {n : ℕ} (rules : Rules n) : Finset (Instance n)
  := {inst | inst ∈ capture rules ∧ inst.tags.Nonempty}
-- The corresponding subtype
def CaptureOnTagged {n : ℕ} (rules : Rules n) := Subtype (· ∈ captureOnTagged rules)

def toPositive {n : ℕ} (rule : Negative n) : Finset (Positive n) :=
  let tags' := (tags rule.val)ᶜ
  -- TODO: Use `Positive.fromTagsEmbedding` here
  let ctor := λ (tag : Tag n) ↦ Positive.fromTags {tag}
  let ctor_inj : ctor.Injective := by
    intro t t' subtype_eq
    have := Subtype.eq_iff.mp subtype_eq
    simp only [Positive.fromTags, positive.injEq, Finset.singleton_inj, ctor] at this
    assumption
  Finset.map ⟨ctor, ctor_inj⟩ tags'

-- What we can show is that for negative rules with exactly one tag, we have a correspondence on the capture between the
-- rule and its positive counterparts, by virtue of the positive rules capturing at least the same instances as the
-- negative rule. Example:
--
-- Tag Universe: {A, B, C, D, E}
-- Negative Rule: N {C}
-- Positive Rules: [P0 {A}, P1 {B}, P2 {D}, P3 {E}]
-- Instances: I0 {A}, I1 {C, D}, I2 {B}
--
-- We then have:
--    appliesTo (N {C}) (I0 {A}) = True (Since {C} ∩ {A} = ∅)
--    appliesTo (N {C}) (I1 {C, D}) = False (Since {C} ∩ {C, D} = {C} ≠ ∅)
--    appliesTo (N {C}) (I2 {B}) = True (Since {C} ∩ {B} = ∅)
--    -> Capture {N {C}} = [I0 {A}, I2 {B}]
--
-- While for the positive rules:
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I0 {A}) = appliesTo (P0 {A}) (I0 {A}) = True (Since {A} ⊆ {A})
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I1 {C, D}) = appliesTo (P2 {D}) (I1 {C, D}) = True (Since {D} ⊆ {C, D})
--    applyTo [P0 {A}, P1 {B}, P2 {D}, P3 {E}] (I2 {B}) = appliesTo (P1 {B}) (I2 {B}) = True (Since {B} ⊆ {B})
--    -> Capture [P0 {A}, P1 {B}, P2 {D}, P3 {E}] = [I0 {A}, I1 {C, D}, I2 {B}] ⊇ [I0 {A}, I2 {B}] = Capture {N {C}}
--
-- Proof idea is as follows:
--    (I) We take an `inst` in the tagged capture (i.e. `inst.tags` is nonempty) of the negative rule.
--    (II) We show that there exists a rule in the positive counterparts that captures the same `inst`.
--      (a) `inst` is covered by a positive counterpart if we can find a tag in `inst.tags` for which such a positive
--          counterpart rule exists.
--      (b) We get that from the fact that `inst` tags are nonempty (tagged capture), so we have at least one `tag'` in
--          `inst.tags` (that must also be different from the negative rule tag, since `inst` is captured by the
--          negative rule).
--      (c) Since `tag'` is different from the `tag` used by the negative rule, there exists a positive counterpart rule
--          with that `tag'`, capturing `inst`.
--
-- Note that the "onTagged"-Restriction is necessary, since e.g. `I {}` would be captured by any negative rule, but no
-- positive counterpart can capture it since it has no tags, and all of our positive counterparts have at least one tag
-- (We would need a tag-less positive rule to capture it).
-- We prove the stronger `captureOnTagged negative ⊆ captureOnTagged positives` here (from which we also have
-- `captureOnTagged negative ⊆ capture positives`, as `captureOnTagged positives ⊆ capture positives`).
theorem captureOnTagged_singleton_negative_sub_captureOnTagged_toPositive
    {n : ℕ}
    (rule : Negative n)
    (rule_val_eq_negative : ∃ tag, rule.val = Rule.negative {tag})
  : captureOnTagged {rule.val} ⊆ captureOnTagged (toPositive rule) := by
    simp [capture, captureOnTagged, toPositive, applyTo, appliesTo, Positive.fromTags]
    intro inst inst_mem_captureOnTagged
    simp [rule_val_eq_negative] at inst_mem_captureOnTagged
    obtain ⟨tag, rule_val_eq_negative_singleton_tag⟩ := rule_val_eq_negative
    simp [rule_val_eq_negative_singleton_tag] at inst_mem_captureOnTagged
    obtain ⟨negative_capture, inst_tags_nonempty⟩ := inst_mem_captureOnTagged
    simp [Finset.mem_filter]
    constructor
    · obtain ⟨tag', tag'_mem_inst_tags⟩ := inst_tags_nonempty
      exists tag'
      constructor
      · intro tag'_mem_rule_tags
        simp [rule_val_eq_negative_singleton_tag] at tag'_mem_rule_tags
        have tag'_mem_inter : tag' ∈ {tag} ∩ inst.tags := Finset.mem_inter_of_mem tag'_mem_rule_tags tag'_mem_inst_tags
        simp [negative_capture] at tag'_mem_inter
      · assumption
    · assumption

theorem captureOnTagged_singleton_negative_sub_captureOnTagged_toPositive'
    {n : ℕ}
    (rule : Negative n)
  : captureOnTagged {rule.val} ⊆ captureOnTagged (toPositive rule) := by
    simp [capture, captureOnTagged, toPositive, applyTo, appliesTo, Positive.fromTags]
    intro inst inst_mem_captureOnTagged
    simp [rule.property] at inst_mem_captureOnTagged
    -- obtain ⟨tag, rule_val_eq_negative_singleton_tag⟩ := rule_val_eq_negative
    obtain ⟨rule_def, inst_tags_nonempty⟩ := inst_mem_captureOnTagged
    -- TODO: `cases rule.val with ...`
    obtain ⟨rule, rule_isNegative⟩ := rule
    simp [rule_isNegative] at rule_def
    sorry
    -- cases rule with
    --   -- | positive tags => exact False.elim (false_of_isPositive_of_isNegative _ _)
    --   | _ =>
    --     simp [rule_val_eq_negative_singleton_tag] at inst_mem_captureOnTagged
    --     obtain ⟨negative_capture, inst_tags_nonempty⟩ := inst_mem_captureOnTagged
    --     simp [Finset.mem_filter]
    --     constructor
    --     · obtain ⟨tag', tag'_mem_inst_tags⟩ := inst_tags_nonempty
    --       exists tag'
    --       constructor
    --       · intro tag'_mem_rule_tags
    --         simp [rule_val_eq_negative_singleton_tag] at tag'_mem_rule_tags
    --         have tag'_mem_inter : tag' ∈ {tag} ∩ inst.tags := Finset.mem_inter_of_mem tag'_mem_rule_tags tag'_mem_inst_tags
    --         simp [negative_capture] at tag'_mem_inter
    --       · assumption
    --     · assumption

-- TODO: Show stuff like `captureOnTagged (positive {t, s}) ⊆ captureOnTagged {positive {t}, positive {s}}` etc.
-- TODO: Maybe also show when the are equal

end Rule
