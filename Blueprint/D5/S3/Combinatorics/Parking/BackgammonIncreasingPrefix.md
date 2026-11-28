# Backgammon parking and first-car insertion

## Abstract

First-car deletion and insertion describe backgammon parking words.

**Definition 1.1 (Backgammon outcome).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammonOutcome`

*Formalization.* `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammonOutcome` (`✓ std3`).

*Citation.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

Cars arrive in label order. The arriving car takes its preference and sends any incumbent to the least vacant spot. Read car labels in spot order.

**Theorem 1.2 (Insert car one in spot one).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammon_first_car_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammon_first_car_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

For a valid reduced word, increase every old preference by one. The new initial preference is either one or one more than an entry of the reduced word's longest distinct initial prefix. These are exactly the valid words with this shifted tail and with car one occupying the first spot of the shifted outcome.

**Theorem 1.3 (Rank of an inserted word).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammon_lift_statistic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammon_lift_statistic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

The lifts of a valid word occur without duplicates and give exactly one word of each longest distinct initial prefix length from one through one more than the reduced word's rank.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammonOutcome`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammon_first_car_insertion`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.backgammon_lift_statistic`
