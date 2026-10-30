/- GID: D5/S1/Recurrence/Residue/HannaA232695Congruences
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaA232695Congruences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S1/Recurrence/Residue/HannaA232695Congruences.result; premises=D5/S1/Recurrence/Residue/HannaA232695Congruences.numerator2,D5/S1/Recurrence/Residue/HannaA232695Congruences.multiple2
   digest: Hanna 232695 factorial coefficients satisfy both nominated congruences. -/

/-
admission_basis: open-problem-resolution (#21486; Proved)
proof_shape: bind-only
escape_witness: D5.S1.Recurrence.Residue.HannaEGFMachinery.residual_transfer
numerator2: proof_shape: bind-only; escape_witness: none; consumer: residual2
multiple2: proof_shape: bind-only; escape_witness: none; consumer: residual2
Literal polynomial substitution and finite coefficient arithmetic are normalization; these consumed helpers supply no escape content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21758.
The rational series equation is stated as printed; coefficient congruences concern n! times coeff n A.
The convolution and power constructions are reused from ExponentialImplicitParityPeriodThree.
-/

import D5.S1.Recurrence.Residue.HannaEGFMachinery

set_option maxHeartbeats 4000000

open PowerSeries
open D5.S1.Recurrence.Residue.IntegralEGFComposition

namespace D5.S1.Recurrence.Residue.HannaA232695Congruences

/-- The source equation over rational formal series; the source data fix A(0)=1. -/
def IsSolution (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧
    PowerSeries.derivative (R := ℚ) A = A.subst (X * (PowerSeries.derivative (R := ℚ) A) ^ 5)

/-- The two nominated OEIS conjectures, on factorial-normalized integer coefficients. -/
def claim : Prop :=
  ∀ A : PowerSeries ℚ, IsSolution A →
    ∃ a : ℕ → ℤ,
      (∀ n : ℕ, eCoeff A n = (a n : ℚ)) ∧
        (∀ n : ℕ, (5 : ℤ) ∣ a n - 1) ∧
        (∀ n : ℕ, 4 ≤ n → (2 : ℤ) ∣ a n)


end D5.S1.Recurrence.Residue.HannaA232695Congruences

open D5.S1.Recurrence.Residue.HannaEGFMachinery
namespace D5.S1.Recurrence.Residue.HannaA232695Congruences

private noncomputable def F2 : PowerSeries ℚ := C (1 : ℚ) * X^0 + C (1 : ℚ) * X^1 + C ((1 / 2) : ℚ) * X^2 + C ((11 / 6) : ℚ) * X^3
private noncomputable def B2 : PowerSeries ℚ := C (1 : ℚ) * X^0 + C (1 : ℚ) * X^1 + C ((11 / 2) : ℚ) * X^2
private noncomputable def N2 : PowerSeries ℚ := (Polynomial.ofCoeffList (R := ℚ) [0,
  0,
  0,
  (-133 / 3),
  (-395 / 2),
  (-4495 / 4),
  (-137899 / 24),
  (-260553 / 8),
  (-1380009 / 8),
  (-6970575 / 8),
  (-32045545 / 8),
  (-136394199 / 8),
  (-2118036827 / 32),
  (-15239243063 / 64),
  (-50297515785 / 64),
  (-308606217095 / 128),
  (-872046773565 / 128),
  (-4589204966313 / 256),
  (-22283504082213 / 512),
  (-50393530471845 / 512),
  (-105076930655785 / 512),
  (-407617493569275 / 1024),
  (-1452673727898481 / 2048),
  (-2399590274914833 / 2048),
  (-3613678092814075 / 2048),
  (-10026854233039215 / 4096),
  (-1562859519333255 / 512),
  (-28429881418033095 / 8192),
  (-28274101245879489 / 8192),
  (-50418851872022865 / 16384),
  (-27790783275864455 / 12288),
  (-47468729197905125 / 32768),
  (-20886240847078255 / 32768),
  (-45949729863572161 / 196608)] : PowerSeries ℚ)
private theorem numerator2 : B2 - (F2.subst (X * B2^5))^1 = N2 := by
  have hs : HasSubst (X * B2^5) := PowerSeries.HasSubst.X'.mul_left
  simp only [F2, subst_add (R := ℚ) hs, subst_mul (R := ℚ) hs,
    subst_pow (R := ℚ) hs, subst_X (R := ℚ) hs, subst_C, ← PowerSeries.C_apply]
  simp only [B2, N2, Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_zero]
  <;> (simp only [PowerSeries.C_eq_algebraMap]; algebra with ℚ)
private theorem multiple2 : Multiple 2 N2 := by
  apply finite_multiple _ [0, 0, 0, -133, -2370, -67425, -2068485, -82074195, -3477622680, -158092641000, -7267929606000, -340276247665200, -15852234827998800, -741367840074661800, -34256652169854114000, -1576392343361620785000, -71272075843003155120000, -3188129905221213456504000, -139323555280706113653336000, -5986451244338984432973960000, -249650269145993039401677600000, -10168731343811022247086822000000, -398634357270825945689398458480000, -15145080066788053119957411912720000, -547387889908426201866841161552000000, -18985429941715537394480382676680000000, -615515526452668923446529770686080000000, -18894608596913876315677484568712440000000, -526150141860363394171358775770940384000000, -13604476570130724824815378135755608880000000, -299950550958002037531877182426681398400000000, -5955928059589209712638011599815509910000000000, -83859467079016072753943203325402379532800000000, -1014699551656094480322712760237368792346880000000] 2
  intro n
  fin_cases n <;> norm_num [List.getElem!_eq_getElem?_getD, Nat.factorial]


private def f2 (n : ℕ) : ℤ := if n < 4 then (([1, 1, 1, 11] : List ℤ)[n]?).getD 0 else 0
private theorem coeff_F2 (n : ℕ) : eCoeff F2 n = (f2 n : ℚ) := by
  by_cases hn : n < 4
  · interval_cases n <;> norm_num [coeff_X, F2, f2, eCoeff]
  · have hne0 : n ≠ 0 := by omega
    have hne1 : n ≠ 1 := by omega
    have hne2 : n ≠ 2 := by omega
    have hne3 : n ≠ 3 := by omega
    simp [F2, f2, eCoeff, coeff_X, hn, hne0, hne1, hne2, hne3]
private theorem F2_derivative : PowerSeries.derivative (R := ℚ) F2 = B2 := by
  simp [F2, B2, Derivation.leibniz, smul_eq_mul]
  <;> (simp only [PowerSeries.C_eq_algebraMap]; algebra with ℚ)
private theorem residual2 : Multiple 2 (PowerSeries.derivative (R := ℚ) F2 - sourceRhs F2 5 1 false) := by
  rw [sourceRhs, F2_derivative]
  simp only [Bool.false_eq_true, if_false]
  rw [numerator2]
  exact multiple2

theorem result : claim := by
  intro A hA
  have he : PowerSeries.derivative (R := ℚ) A = sourceRhs A 5 1 false := by simpa [sourceRhs] using hA.2
  obtain ⟨a,ha,hm⟩ := residual_transfer A F2 5 1 2 false hA.1 he f2 (coeff_F2) (by norm_num [f2]) (by simp) residual2
  obtain ⟨b,hb,hbmod⟩ := residual_transfer A (exp ℚ) 5 1 5 false hA.1 he (fun _ => 1) (by simp) rfl (by simp)
    (by simpa [sourceRhs] using D5.S1.Recurrence.Residue.HannaEGFMachinery.exp_residual 5 5 (fun n => D5.S1.Recurrence.Residue.HannaEGFMachinery.expSum_mod 5 5 n (dvd_refl 5)))
  have hab : a = b := by
    funext n
    have hh := (ha n).symm.trans (hb n)
    exact_mod_cast hh
  refine ⟨a,ha,?_,?_⟩
  · intro n
    rw [hab]
    exact hbmod n
  · intro n hn
    simpa [f2, Nat.not_lt.mpr hn] using hm n


end D5.S1.Recurrence.Residue.HannaA232695Congruences
