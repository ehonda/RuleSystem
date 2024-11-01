# Proof overview

The purpose of this document is to provide an overview of what we have proven so far and what's currently open / in
progess. Legend:

* ✅ Proven
* 🚧 In progress
* ❓ Open

The following sections display status by topic. We use kind of a pseudo notation which closely resembles the correct lean syntax but is optimized for "informal readability".

Additionally, we number them kind of arbitrarily to make them easier to succinctly reference. This way we can also track in code which theorems are tracked by this document.

## Embeddings

Here we denote `captureFromSingle` by `capture`.

### Positive

* `(EP-0): rule.capture.castSucc ⊆ rule.castSucc.capture` ✅
* `(EP-1): rule.capture.castSucc ⊂ rule.castSucc.capture` ✅
* `(EP-2): rule.capture.castSucc = rule.castSucc.capture \ Instances.containingLast` ✅

### Negative

## Splits
