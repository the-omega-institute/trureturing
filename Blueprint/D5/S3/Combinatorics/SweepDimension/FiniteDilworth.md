# Finite Dilworth chain covers

## Abstract

A finite poset admits a chain cover with no more chains than the size of a maximum antichain.

**Definition 1.1 (Maximum antichain size).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.maxAntichainSize`

*Formalization.* `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.maxAntichainSize` (`✓ std3`).

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Dilworth's decomposition theorem*. URL: <https://github.com/facebookresearch/atlas-lean/blob/98c0ecc1f951837620cbd8e75c6ce27942f496c0/MathlibExt/Combinatorics/Order/Dilworth.lean>.

*Commentary.*

Width is the maximum cardinality of an antichain of the finite poset.

**Theorem 1.2 (The width bounds every antichain).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.card_le_maxAntichainSize`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.card_le_maxAntichainSize` (`✓ std3`). ∎

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Dilworth's decomposition theorem*. URL: <https://github.com/facebookresearch/atlas-lean/blob/98c0ecc1f951837620cbd8e75c6ce27942f496c0/MathlibExt/Combinatorics/Order/Dilworth.lean>.

*Commentary.*

Every antichain has cardinality at most the width.

**Theorem 1.3 (A maximum antichain exists).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.exists_isAntichain_card_eq_maxAntichainSize`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.exists_isAntichain_card_eq_maxAntichainSize` (`✓ std3`). ∎

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Dilworth's decomposition theorem*. URL: <https://github.com/facebookresearch/atlas-lean/blob/98c0ecc1f951837620cbd8e75c6ce27942f496c0/MathlibExt/Combinatorics/Order/Dilworth.lean>.

*Commentary.*

Some antichain attains the width, including the empty carrier case.

**Theorem 1.4 (A cover by at most width many chains).**

Lean statement: `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.exists_chain_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.exists_chain_cover` (`✓ std3`). ∎

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Dilworth's decomposition theorem*. URL: <https://github.com/facebookresearch/atlas-lean/blob/98c0ecc1f951837620cbd8e75c6ce27942f496c0/MathlibExt/Combinatorics/Order/Dilworth.lean>.

*Commentary.*

There is a finite family of chains covering every point, whose cardinality is at most the width. This is the finite Dilworth chain-cover theorem; the supplied proof splits at a maximum antichain and joins the resulting chain covers.

## References

- Truth anchor: `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.card_le_maxAntichainSize`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.exists_chain_cover`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.exists_isAntichain_card_eq_maxAntichainSize`
- Truth anchor: `D5/S3/Combinatorics/SweepDimension/FiniteDilworth.maxAntichainSize`
