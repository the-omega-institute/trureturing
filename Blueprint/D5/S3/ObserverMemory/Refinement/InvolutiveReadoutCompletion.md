# Involutive Readout Completion

## Abstract

A readout flipped by an involution at every step is restored at even depth and remains visibly flipped at odd depth.

**Theorem 1.1 (Even iterates complete the chosen readout).**

$$\operatorname{Even}(n) \Rightarrow \operatorname{readout}(\operatorname{step}^n(state)) = \operatorname{readout}(state).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion.even_iterate_completes_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When one update applies an involution to the selected readout, every even number of updates restores that readout.

The state update itself need not be involutive, so readout completion does not imply return of the complete hidden state.

**Theorem 1.2 (Odd iterates preserve a visible flip).**

$$(\operatorname{Odd}(n) \land \operatorname{flip}(\operatorname{readout}(state)) \neq \operatorname{readout}(state)) \Rightarrow \operatorname{readout}(\operatorname{step}^n(state)) \neq \operatorname{readout}(state).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion.odd_iterate_breaks_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the starting readout is not fixed by the involution, every odd iterate is distinguished from the starting readout.

This is the reusable formal core of the phrase odd breaking and even completion. It applies only to an explicitly involutive readout.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion.even_iterate_completes_readout`
- Truth anchor: `D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion.odd_iterate_breaks_readout`
