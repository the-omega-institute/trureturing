# Four registers in one visited frame

## Abstract

Four registers in one visited frame.

The same finite program applies the single-register phase successively to four fixed targets. Already completed targets are retained; each remaining target is blank when entered. The packed tape and unrelated tracks are unchanged.

The four phases share a single head interval. Their finite transitions and actual costs compose into one run, while storage is bounded by historical positions in that interval. The final tapes contain the four separately normalized packed lanes.

**Theorem 1.1 (all registers).**

Lean statement: `D5/S0/Computability/WindowRegisterComposition.all_registers`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowRegisterComposition.all_registers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: all_registers (m : Track → ℤ → Symbol) (h : Track → ℤ) (bs : List Bits) (W : ℕ) (hW : bs.length+2 ≤ W) (hh : ∀ t,0≤h t ∧ h t≤W) (hw : h workTrack=0) (hj : ∀ j : Lane,h (target j)=0) (mw : m workTrack=word bs) (mj : ∀ j : Lane,m (target j)=fun _=>.blank) : ∃ T : ℕ, T≤128*(bs.length+1)+4 ∧ run (entry m h 0) T=startAt m h bs 4 ∧ program (startAt m h bs 4).control=.halt ∧ (∀ n≤T,Heads W (run (entry m h 0) n)) ∧ ∀ j : Lane,(startAt m h bs 4).cell (target j)=register bs j

## References

- Truth anchor: `D5/S0/Computability/WindowRegisterComposition.all_registers`
- Dependency: [D5/S0/Computability/WindowRegisterTrim](WindowRegisterTrim.md)
