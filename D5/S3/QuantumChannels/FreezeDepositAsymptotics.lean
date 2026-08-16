/- GID: D5/S3/QuantumChannels/FreezeDepositAsymptotics
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict freeze-deposit bound and asymptotic limits at infinite and zero beta. -/

import Mathlib
import D5.S3.QuantumChannels.FreezeTrichotomy

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT (2026-08-16, pinned repository and pinned mathlib):
   * `D5/S3/QuantumChannels/DecoherenceFreeze.lean:13-14` defines `freezeDeposit` as
     `passiveEnergy - entropyTax / beta`.
   * `D5/S3/QuantumChannels/FreezeTrichotomy.lean:53-73` supplies strict increase and the
     non-strict passive-energy upper bound, but no asymptotic result.
   * `Mathlib/Topology/Algebra/Order/Field.lean:60-62` provides
     `tendsto_inv_nhdsGT_zero`, exactly the positive-side reciprocal limit needed below.
   * `Mathlib/Topology/Algebra/Order/Field.lean:222-224` provides
     `Filter.Tendsto.const_div_atTop`, including arbitrary real numerators.
   * `Mathlib/Topology/Algebra/Group/Defs.lean:140-143` generates `Filter.Tendsto.sub`,
     used to subtract the vanishing quotient from the constant passive energy.
   * `Mathlib/Order/Filter/AtTopBot/Field.lean:69-74` and lines 264-268 provide positive
     and negative constant scaling at infinity.
   * `Mathlib/Order/Filter/AtTopBot/Group.lean:68-76` generates the additive constant-shift
     lemmas used to preserve `atBot`.
   * `Mathlib/Topology/Defs/Filter.lean:113,155` defines `𝓝[>] 0` to be exactly
     `nhdsWithin 0 (Set.Ioi 0)`, so the source filter states positive-side convergence.
   * `Mathlib/Algebra/Order/Group/Unbundled/Basic.lean:245-249` generates
     `sub_lt_self_iff`, and `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:880-881`
     provides `div_pos` for the strict finite bound.
   * A repository search found `freezeDeposit` only in the two frozen files above and found
     no existing `Tendsto` theorem for it.

   Assumption audit: the `beta -> atTop` theorem needs no sign condition on the tax. For the
   positive-side zero limit, `entropyTax = 0` makes the deposit constantly `passiveEnergy`,
   while a negative tax makes it diverge to `atTop`; hence `0 < entropyTax` is sharp. For the
   strict bound, a zero tax or zero beta gives equality, while a negative beta reverses the
   sign of the quotient, so both positivity assumptions are load-bearing. -/

namespace D5.S3.QuantumChannels.FreezeDepositAsymptotics

open Filter
open D5.S3.QuantumChannels.DecoherenceFreeze

/-- A positive entropy tax at positive inverse temperature leaves a strict gap below the
passive-energy shift. -/
theorem freeze_deposit_lt_passive_energy_of_pos_tax
    {beta entropyTax passiveEnergy : ℝ} (hbeta : 0 < beta) (htax : 0 < entropyTax) :
    freezeDeposit beta entropyTax passiveEnergy < passiveEnergy := by
  rw [freezeDeposit, sub_lt_self_iff]
  exact div_pos htax hbeta

/-- At infinite inverse temperature, the entropy-tax correction vanishes for every real tax. -/
theorem freeze_deposit_tendsto_passive_energy (entropyTax passiveEnergy : ℝ) :
    Filter.Tendsto (fun beta : ℝ => freezeDeposit beta entropyTax passiveEnergy)
      Filter.atTop (nhds passiveEnergy) := by
  simpa [freezeDeposit] using
    (tendsto_const_nhds.sub (tendsto_id.const_div_atTop entropyTax))

/-- With a positive entropy tax, the freeze deposit diverges to negative infinity as inverse
temperature approaches zero through positive values. -/
theorem freeze_deposit_tendsto_atBot_of_pos_tax
    {entropyTax passiveEnergy : ℝ} (htax : 0 < entropyTax) :
    Filter.Tendsto (fun beta : ℝ => freezeDeposit beta entropyTax passiveEnergy)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
  have hquot :
      Filter.Tendsto (fun beta : ℝ => entropyTax / beta)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa [div_eq_mul_inv] using
      Filter.Tendsto.const_mul_atTop htax
        (tendsto_inv_nhdsGT_zero :
          Filter.Tendsto (fun beta : ℝ => beta⁻¹)
            (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
  have hneg :
      Filter.Tendsto (fun beta : ℝ => -(entropyTax / beta))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
    simpa using
      Filter.Tendsto.const_mul_atTop_of_neg (show (-1 : ℝ) < 0 by norm_num) hquot
  simpa [freezeDeposit, sub_eq_add_neg] using
    tendsto_atBot_add_const_left _ passiveEnergy hneg

#print axioms freeze_deposit_lt_passive_energy_of_pos_tax
#print axioms freeze_deposit_tendsto_passive_energy
#print axioms freeze_deposit_tendsto_atBot_of_pos_tax

end D5.S3.QuantumChannels.FreezeDepositAsymptotics
