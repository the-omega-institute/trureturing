/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Exact width-six HDA transfer with two defects. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635RowCertificate
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Starts

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer

open HardinA229584StripData (Row horizontal)
open WidthSix
open HardinA233177Canonical (Canonical canonical_exists_unique)
open HardinA229635State HardinA229635Laws HardinA229635Starts
open HardinA229635Rows HardinA229635RowCertificate

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def T (i j : State) : ℤ :=
  Fin.addCases (m := 31) (n := 96)
    (fun k => Fin.addCases (m := 31) (n := 96) (HardinA229532StripData.T k) (fun _ => 0) j)
    (fun k => ((weights k).count j : ℤ)) i

def initial (s : State) : ℤ := if s.val < 31 then 0 else 6

def terminal (s : State) : ℤ :=
  Fin.addCases (m := 31) (n := 96) HardinA229532StripData.terminal
    (fun i => if budget i = 0 then 1 else 0) s

private theorem inherited_valid (p : Row) (d : ℕ) (hp : h p + d ≤ 1) :
    HardinA229532StripData.Valid p d := by
  change d ≤ 1 ∧ h p ≤ 1 - d
  omega

private theorem old_cl (p : Row) (d : ℕ) (hpd : h p + d ≤ 1) :
    cl p d = (HardinA229532StripData.cl p d).castAdd 96 := by simp only [cl, ite_eq_left hpd]

private theorem old_counts (p : Row) (d : ℕ) (hp : h p + d ≤ 1) (s : State) :
    (∑ r : Row, if cost p r ≤ d ∧ cl r (d - cost p r) = s then (1 : ℤ) else 0) =
      T (cl p d) s := by
  rw [old_cl p d hp]
  refine Fin.addCases (m := 31) (n := 96) ?_ ?_ s
  · intro j
    rw [T, Fin.addCases_left, Fin.addCases_left]
    have he (r : Row) :
        (cost p r ≤ d ∧ cl r (d - cost p r) = j.castAdd 96) ↔
        (cost p r ≤ d ∧ HardinA229532StripData.cl r (d - cost p r) = j) := by
      by_cases hr : cost p r ≤ d
      · simp only [hr, true_and, old_cl _ _ (closed p r d hp hr)]
        exact (Fin.castAdd_injective 31 96).eq_iff
      · simp [hr]
    simp_rw [he]
    let budget : Fin 2 := ⟨d, by omega⟩
    exact HardinA229532Strip.finite_certificate.2.2.1 p budget (inherited_valid p d hp) j
  · intro j
    rw [T, Fin.addCases_left, Fin.addCases_right]
    have hzero (r : Row) : ¬ (cost p r ≤ d ∧ cl r (d - cost p r) = j.natAdd 31) := by
      rintro ⟨hr, hc⟩
      rw [old_cl _ _ (closed p r d hp hr)] at hc
      have hv := congrArg Fin.val hc
      have hl := (HardinA229532StripData.cl r (d - cost p r)).isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp_rw [ite_eq_right (hzero _), Finset.sum_const_zero]

private theorem sum_relabel (p : Row) (d : ℕ) (s : State) (e : Equiv.Perm (Fin 3)) :
    (∑ r : Row, if cost (e ∘ p) r ≤ d ∧ cl r (d - cost (e ∘ p) r) = s
      then (1 : ℤ) else 0) =
    ∑ r : Row, if cost p r ≤ d ∧ cl r (d - cost p r) = s then (1 : ℤ) else 0 := by
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
  conv_lhs =>
    rw [← E.sum_comp]
  change (∑ r : Row, if cost (e ∘ p) (e ∘ r) ≤ d ∧
      cl (e ∘ r) (d - cost (e ∘ p) (e ∘ r)) = s then (1 : ℤ) else 0) = _
  simp only [cost_relabel, cl_relabel]

private theorem fresh_counts (p : Row) (d : ℕ) (hp : h p + d = 2) (hn : Canonical p)
    (s : State) :
    (∑ r : Row, if cost p r ≤ d ∧ cl r (d - cost p r) = s then (1 : ℤ) else 0) =
      T (cl p d) s := by
  have he := representatives_complete p hn (by omega)
  have hd : budget (fresh p) = d := by
    unfold budget
    rw [he]
    omega
  rw [cl, ite_eq_right (by omega), T, Fin.addCases_right, ← outgoing_count,
    ← checked_weights, he, hd]

theorem transition_counts (p : Row) (d : ℕ) (hp : Valid p d) (s : State) :
    (∑ r : Row, if cost p r ≤ d ∧ cl r (d - cost p r) = s then (1 : ℤ) else 0) =
      T (cl p d) s := by
  by_cases hold : h p + d ≤ 1
  · exact old_counts p d hold s
  · obtain ⟨q, ⟨hq, e, he⟩, _⟩ := canonical_exists_unique p
    unfold Valid at hp
    calc
      _ = ∑ r : Row, if cost q r ≤ d ∧ cl r (d - cost q r) = s then (1 : ℤ) else 0 := by
        rw [he, sum_relabel]
      _ = T (cl q d) s := fresh_counts q d (by rw [he, h_relabel]; omega) hq s
      _ = _ := by rw [he, cl_relabel]

theorem terminal_correct (p : Row) (d : ℕ) (hp : Valid p d) :
    terminal (cl p d) = if d = 0 then 1 else 0 := by
  by_cases hold : h p + d ≤ 1
  · rw [old_cl p d hold, terminal, Fin.addCases_left]
    let budget : Fin 2 := ⟨d, by omega⟩
    exact HardinA229532Strip.finite_certificate.1 p budget (inherited_valid p d hold)
  · obtain ⟨q, ⟨hq, e, he⟩, _⟩ := canonical_exists_unique p
    have hq' : h q + d = 2 := by unfold Valid at hp; rw [he, h_relabel]; omega
    have hr := representatives_complete q hq (by omega)
    have hd : budget (fresh q) = d := by unfold budget; rw [hr]; omega
    have hc : cl p d = cl q d := by rw [he, cl_relabel]
    rw [hc, cl, ite_eq_right (by omega), terminal, Fin.addCases_right, hd]

theorem initial_correct (s : State) :
    (∑ r : Row, if h r ≤ 2 ∧ cl r (2 - h r) = s then (1 : ℤ) else 0) = initial s := by
  rw [← start_count, checked_starts]
  exact start_tallies s

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer
