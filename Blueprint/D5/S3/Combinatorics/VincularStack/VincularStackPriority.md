# Priority of Maximum Insertion Sites

## Abstract

Two inserted maxima retain the order prescribed by their original output gaps.

**Theorem 1.1 (The two adjacent sites remain active).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackPriority.adjacent_sites_active`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackPriority.adjacent_sites_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Let a word have distinct entries, let M exceed them all, and let L exceed M. If inserting M at a gap gives an SC output avoiding 231, then inserting L immediately before M or immediately after M also gives an SC output avoiding 231.

**Theorem 1.2 (Ordering two inserted entries).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackPriority.two_marker_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackPriority.two_marker_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Choose two distinct input gaps, the first strictly earlier than the second, and insert at them two entries each greater than every original entry. The original SC output splits into three consecutive words, and the two inserted entries occur between those words at their original output gaps. The entry with the smaller output gap comes first; when the output gaps coincide, the entry at the earlier input gap comes first. Deleting the two inserted entries recovers the original SC output.

**Theorem 1.3 (Activity at a later site).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackPriority.later_site_activity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackPriority.later_site_activity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Let a word have distinct entries, let M exceed them all, and let L exceed M. Suppose insertion of M at an earlier gap gives an SC output avoiding 231. Inserting L at a strictly later input gap in that word gives an SC output avoiding 231 if and only if inserting L at that gap in the original word does so and the later gap has a strictly smaller original output gap than the gap chosen for M.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackPriority.adjacent_sites_active`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackPriority.later_site_activity`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackPriority.two_marker_order`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackCharacterization](VincularStackCharacterization.md)
