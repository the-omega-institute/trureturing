# Critical renewal actual one-gap law and estimates

## Abstract

Actual terminal marks and their uniform source-specific estimates.

**Theorem 1.1 (A mark from its own actual gap).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap.block_pair_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap.block_pair_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural J, any duration mass function f and immutable Tick J, the pushforward of blockLaw f t under b mapped to (length(b.zeros),increment(t,b)) is exactly pairLaw f t.

zeroTraceLaw starts with the empty zero history and phase zero. At each successive zero it samples the capped phase coin at the current phase and appends the outcome, retaining the terminal phase as a proof coordinate. markedTraceLaw then samples the one tick coin at that phase. The resulting Block contains only the finite zero outcomes and its tick outcome; its duration is the length of that very history.

The support induction identifies both the trace length and terminal phase, and the marginal phase induction gives GeometricPhaseOccupation.finiteCappedLaw. Thus the potential pair is the duration and mark of these same coins, with no independence claim inside a pair.

**Theorem 1.2 (Uniform source-specific one-gap estimates).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap.uniform_one_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap.uniform_one_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural r>=1 and a real c>0. There are eta and sStar in (0,1) and positive Dlo,Dhi,Cmean,Csecond,Vzero, all chosen before s and J, with Vzero=4 Csecond+2 Cmean. For every 0<s<sStar and every integer J>=1 satisfying s 2^J<=eta, put I=s^(2r) J and delta=J/2^(r J). The source PMF f_i is exactly CriticalRenewalSource.gapLaw: at each k>=1 its unnormalized mass is k^(2r-1) exp(-s k) for i=false, and (k^(2r-1)+c k^(r-1)) exp(-s k) for i=true, normalized separately; its mass at zero is zero.

The phase PMF is f_i bound to GeometricPhaseOccupation.finiteCappedLaw J. Its live Lean phase index j has source phase number j+1; index J is dead. A live terminal phase z has reward 2^(-r(z+1)); the dead reward is zero. Define m_i as the mean of this single terminal reward, theta=(m_0+m_1)/2, and Delta=m_1-m_0. Then I>0, 0<delta<=1/2, Dlo I<=Delta<=Dhi I, 0<=m_i<=Cmean s^(2r) 2^(r J), and the mean of the square of the one terminal reward is at most Csecond I. At every phase 0<=reward<=2^(-r), and 0<=theta<=2^(-r), with theta^2<=Csecond I.

For every source label and every live phase j, its actual terminal probability is (A_(j+1)^(2r-1)+c A_(j+1)^(r-1) for label one, or A_(j+1)^(2r-1) for label zero)/Z_i. Accordingly Delta is exactly c/Z_1 times [sum_(j=1)^J 2^(-r j) A_j^(r-1) - g(s) sum_(j=1)^J 2^(-r j) A_j^(2r-1)]. The factor c/Z_1 and the negative normalizer correction are both retained.

The common immutable Tick is roundedTick reward theta delta. At every phase z its lower entry is n_z=floor((reward(z)-theta)/delta), and its fresh Bernoulli upper probability is p_z=(reward(z)-theta)/delta-n_z, with 0<=p_z<1. On a Boolean upper outcome b its integer increment is n_z+1 for b=true and n_z otherwise. Every possible phase/outcome satisfies abs(delta increment)<=1, including the dead phase and unused zero-gap tick rows.

The actual joint PMF is CriticalRenewalTable.pairLaw f_i Tick: draw k from the exact source PMF, then its capped phase after exactly k zeros, then that phase's fresh tick. The score U=delta times the integer tick increment and its square are integrable under this same joint law. Their actual integrals satisfy E_0 U=-Delta/2, E_1 U=Delta/2 and E_i U^2<=Vzero I. No independence between U and k is asserted. The finite phase/tick law used to compute these marginals is a mathematical distribution and adds no persistent controller configuration.

The proof directly reuses uniform_discounted_phase_occupation at source phase j+1 and the source module's exact laws and common scalar neighborhood. Write b=lowerConstant(r-1), B=upperConstant(r-1), and Cstar=upperConstant(2r-1)/(1-2^(-r)). With zlo,zhi,G from the common source neighborhood, choose eta=min(1/2,b/(2 G Cstar)), Dlo=c b/(2 zhi), Dhi=c B/zlo, Cmean=(1+c) Cstar/zlo, and Csecond=(1+c) upperConstant(2r-1)/zlo. The uniform scale condition makes the negative correction at most b/2, while the positive occupation sum is between b J and B J. Exactly one phase reward is squared before averaging.

For every signed x, adjacent-grid rounding is unbiased and has square mean x^2+delta^2 p(1-p). The signed floor cells give delta^2 p(1-p)<=delta abs(x), including negative x and grid points, and each outcome has magnitude at most abs(x)+delta. Applying this to x=reward-theta gives E_i x^2<=4 Csecond I and delta E_i abs(x)<=2 Cmean I. These two bounds yield Vzero=4 Csecond+2 Cmean; an unconditional delta^2 allowance per gap is not used. The reward and theta bounds and delta<=1/2 give the pointwise unit score bound.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap.block_pair_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap.uniform_one_gap`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable](CriticalRenewalTable.md)
