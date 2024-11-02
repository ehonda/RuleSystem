# Theorem overview

The purpose of this document is to provide an overview of the _main_ theorems we have proven so far (there are more but
we don't want to label and track them all if they are more of auxilliary nature) and what's currently open
/ in progess. Legend:

* ✅ Proven
* 🚧 In progress
* ❓ Open
* 🚮 Obsolete

The following sections display status by topic. We use kind of a pseudo notation which closely resembles the correct
lean syntax but is optimized for "informal readability".

Additionally, we number them kind of arbitrarily to make them easier to succinctly reference. This way we can also track
in code which theorems are tracked by this document.

## Embeddings

Here we denote the `-fromSingle` versions of the capture functions by just their prefix, e.g. `captureFromSingle` by
`capture`.

### Positive

* `(EP-0): rule.capture.castSucc ⊆ rule.castSucc.capture` ✅
* `(EP-1): rule.capture.castSucc ⊂ rule.castSucc.capture` ✅
* `(EP-2): rule.capture.castSucc = rule.castSucc.capture \ Instances.containingLast` ✅

### Negative

* `(EN-0): rule.captureOnTagged.castSucc ⊆ rule.castSucc.captureOnTagged` 🚮
* `(EN-1): rule.captureOnTagged.castSucc ⊂ rule.castSucc.captureOnTagged` ✅
* `(EN-0') rule.capture.castSucc ⊆ rule.castSucc.capture` ✅
* `(EN-1') rule.capture.castSucc ⊂ rule.castSucc.capture` ❓

## Splits

TODO: Fill this section

## Others

TODO: Fill this section
