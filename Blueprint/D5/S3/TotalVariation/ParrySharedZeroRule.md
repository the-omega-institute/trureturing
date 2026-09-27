# Complete zero runs and the shared window rule

## Abstract

Complete zero runs under the stationary Parry path law.

For a Boolean window of length R, windowOnes records its one positions. The function sharedRule applies the longest complete zero-run selector: both bounding ones must lie in the window, length is primary, and the latest closing endpoint wins ties. Its value is the parity of zero bits strictly after that closing one, with value false when there is no complete candidate. Thus the physical anchor is the vertex immediately after the closing one. This function depends only on R and the observed window, with no source parameter k.

**Theorem 1.1 (Forward and reversed complete-run cylinders).**

Lean statement: `D5/S3/TotalVariation/ParrySharedZeroRule.parry_complete_run_laws`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParrySharedZeroRule.parry_complete_run_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k >= 2, p = parryParameter k, and q = 1-p. For any finite list of pairs (z,w) with z >= 1 and 1 <= w < k, form the continuation by concatenating 0^(z-1), 1^w, and a final zero for each pair. After the initial boundary 10, its first zero is already observed; each subsequent final zero begins the next block. The stationary mass of this entire word, divided by the stationary mass of 10, equals the product over the list of (q p^(z-1)) (p^(w+1)/q). The same product is obtained for the reversed entire word divided by the stationary mass of 01. In the latter case the runs are read toward the past from the final 01 boundary. Both denominators are positive. These are identities for sums of the actual finite state-path weights. Reset transitions and increment transitions evaluate each run, while summing the starting state uses the stationary Parry law. The identities impose neither independence assumptions nor window-containment conditioning.

**Theorem 1.2 (Uniform bound for an empty complete-run window).**

Lean statement: `D5/S3/TotalVariation/ParrySharedZeroRule.parry_no_complete_run_bound`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParrySharedZeroRule.parry_no_complete_run_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k >= 2 and every natural R, the R-transition path mass of having no complete zero-run candidate is at most (31/32)^(R/4), where R/4 denotes natural-number division. This holds from every signed starting state. It also holds for the event that the new R-bit window in the stationary (R+1)-transition prefix has no selected candidate. From any starting suffix j, the four-bit word 0101 has mass p^4 h_1/h_j >= p^5 >= 1/32 and contains the complete zero run bounded at positions 1 and 3. A complete candidate in a suffix remains complete in the whole window. Successive four-transition decompositions sum over their actual intermediate states; removing the displayed path costs at least 1/32 of each row mass. The remaining fewer than four transitions require only the probability bound one. This argument does not require independent blocks.

These run-cylinder identities and the empty-window estimate do not yet bound the transport defect of sharedRule. Such a bound additionally requires control of selected-anchor entry and expiration, discrete maximum ties, and the probability that the necessary complete runs extend beyond the window.

## References

- Truth anchor: `D5/S3/TotalVariation/ParrySharedZeroRule.parry_complete_run_laws`
- Truth anchor: `D5/S3/TotalVariation/ParrySharedZeroRule.parry_no_complete_run_bound`
- Dependency: [D5/S3/ObserverMemory/Trajectories/LongestZeroSelectorResponse](../ObserverMemory/Trajectories/LongestZeroSelectorResponse.md)
- Dependency: [D5/S3/TotalVariation/ParryTwistedComparison](ParryTwistedComparison.md)
- Dependency: [D5/S3/TotalVariation/ParryWordCollision](ParryWordCollision.md)
