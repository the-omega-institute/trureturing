/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Tactic.Attr.Register

/-!
# Named simp sets for Econlib

Simp attributes must be declared in a file imported by their use sites, so they are collected here.
These sets exist so that *sum-unfolding* evaluation lemmas stay out of the default simp set (where
they would explode every `FinDist.expect` / `signalingValue` in theoretical files into
`Finset.sum`s) while remaining available to worked examples as one-word simp arguments.

* `findist_eval` — evaluation lemmas for `FinDist`: Unfold `expect` to a weighted sum, evaluate
  point masses, priors, and mixtures coordinatewise. Finite worked examples use it to reduce
  probability expressions to concrete arithmetic.
* `signaling_eval` — evaluation lemmas for signaling games: The `_eq_sum` / `_eq_expect` equation
  lemmas for `marginalProb`, `senderExpectedPayoff`, `receiverExpectedPayoff`,
  `receiverPosteriorPayoff`, `equilibriumPayoff`, and `signalingValue`, plus the `mkFin` carrier
  lemmas. Layered on top of `findist_eval`: A typical example closes leaf goals with
  `simp [findist_eval, signaling_eval, <game payoff defs>] <;> norm_num`.

Caveat for `signaling_eval` consumers: A game built via `SignalingGame.mkFin` must be bound with
`abbrev` (or `@[reducible] def`) — with a plain `def`, statements about the game fail to
*elaborate* (no `OfNat`/`DecidableEq` instances on the opaque carriers), before any simp set is
consulted. This restates the requirement in `mkFin`'s docstring; the simp sets cannot relax it.
-/

register_simp_attr findist_eval

register_simp_attr signaling_eval
