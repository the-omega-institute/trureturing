/- GID: D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.claim; result=D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.result; claim=D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.claim
   digest: A rational qutrit measurement beats both error-disturbance endpoints. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation
import D5.S3.Weil.ZetaLinear.RankTrace

/-! Exact state bounds for a rational three-dimensional measurement. -/

set_option maxRecDepth 2048
set_option autoImplicit false
set_option linter.style.longLine false
open scoped BigOperators ComplexOrder Matrix
open Matrix
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation (measurementProjector)

namespace D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation

noncomputable section

/-- The infinity distance between the two labeled outcome distributions. -/
def errorAt {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (a c : unitaryGroup (Fin d) ℂ) : ℝ :=
  ⨆ i, |(trace (ρ * (measurementProjector a i - measurementProjector c i))).re|

/-- The infinity distance before and after the nonselective intermediate measurement. -/
def disturbanceAt {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (c b : unitaryGroup (Fin d) ℂ) : ℝ :=
  ⨆ j, |(trace (ρ * (measurementProjector b j -
    ∑ k, measurementProjector c k * measurementProjector b j * measurementProjector c k))).re|

/-- The supremum of the sum, over one common density matrix. -/
def overallError {d : ℕ} (a c b : unitaryGroup (Fin d) ℂ) : ℝ :=
  sSup {t | ∃ ρ, IsDensity ρ ∧ t = errorAt ρ a c + disturbanceAt ρ c b}

/-- The worst state-dependent labeled error. -/
def error {d : ℕ} (a c : unitaryGroup (Fin d) ℂ) : ℝ :=
  sSup {t | ∃ ρ, IsDensity ρ ∧ t = errorAt ρ a c}

/-- The worst state-dependent disturbance. -/
def disturbance {d : ℕ} (c b : unitaryGroup (Fin d) ℂ) : ℝ :=
  sSup {t | ∃ ρ, IsDensity ρ ∧ t = disturbanceAt ρ c b}

/-- Relabel the columns of a measurement basis. -/
def relabel {d : ℕ} (b : unitaryGroup (Fin d) ℂ) (π : Equiv.Perm (Fin d)) :
    unitaryGroup (Fin d) ℂ :=
  ⟨b.val.submatrix (Equiv.refl _) π, Matrix.submatrix_equiv_mem_unitary.mpr b.property⟩

/-- The minimum error over all outcome relabelings. -/
def relaxedError {d : ℕ} (a b : unitaryGroup (Fin d) ℂ) : ℝ :=
  ⨅ π : Equiv.Perm (Fin d), error a (relabel b π)

/-- The second inequality of Zhou, Wu and Chau's Conjecture 3. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a c b : unitaryGroup (Fin d) ℂ,
    min (relaxedError a b) (disturbance a b) ≤ overallError a c b

private def u : Matrix (Fin 3) (Fin 3) ℂ :=
  !![312/313, -25/313, 0; 25/313, 312/313, 0; 0, 0, 1]

private def v : Matrix (Fin 3) (Fin 3) ℂ :=
  !![32976/33205, -3757/33205, -1020/33205;
     3893/33205, 31824/33205, 8640/33205; 0, -8700/33205, 32045/33205]

private lemma u_unitary : u ∈ unitaryGroup (Fin 3) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change u * uᴴ = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [u, Matrix.mul_apply, Matrix.conjTranspose_apply, map_ofNat, Fin.sum_univ_three]

private lemma v_unitary : v ∈ unitaryGroup (Fin 3) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change v * vᴴ = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [v, Matrix.mul_apply, Matrix.conjTranspose_apply, map_ofNat, Fin.sum_univ_three]

private def c : unitaryGroup (Fin 3) ℂ := ⟨u, u_unitary⟩
private def b : unitaryGroup (Fin 3) ℂ := ⟨v, v_unitary⟩

private def e (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  measurementProjector 1 i - measurementProjector c i

private def f (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  measurementProjector b j -
    ∑ k, measurementProjector c k * measurementProjector b j * measurementProjector c k

private lemma projector_apply {d : ℕ} (a : unitaryGroup (Fin d) ℂ)
    (i j k : Fin d) : measurementProjector a i j k = a.val j i * star (a.val k i) := rfl

private lemma e_table (i : Fin 3) : e i =
  ![!![(625/97969), (-7800/97969), 0; (-7800/97969), (-625/97969), 0; 0, 0, 0],
    !![(-625/97969), (7800/97969), 0; (7800/97969), (625/97969), 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 0; 0, 0, 0]] i := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [e, projector_apply, c, u, Matrix.one_apply]

private lemma f_table (j : Fin 3) : f j =
  ![!![(-48223663488/8071854892201), (7474590559128/201796372305025), 0; (7474590559128/201796372305025), (48223663488/8071854892201), 0; 0, 0, 0],
    !![(2355291948417408/423296142401912641), (-365066477498370648/10582403560047816025), (45084/1520789); (-365066477498370648/10582403560047816025), (-2355291948417408/423296142401912641), (-381888/1520789); (45084/1520789), (-381888/1520789), 0],
    !![(173605188556800/423296142401912641), (-1076341040514432/423296142401912641), (-45084/1520789); (-1076341040514432/423296142401912641), (-173605188556800/423296142401912641), (381888/1520789); (-45084/1520789), (381888/1520789), 0]] j := by
  ext k l
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [f, projector_apply, c, b, u, v, Matrix.mul_apply,
      Matrix.sum_apply, map_ofNat, Fin.sum_univ_three]

private lemma psd_of_ldl {h : Matrix (Fin 3) (Fin 3) ℂ}
    (l : Matrix (Fin 3) (Fin 3) ℂ) (d : Fin 3 → ℝ) (hd : ∀ k, 0 ≤ d k)
    (heq : h = l * diagonal (fun k => (d k : ℂ)) * lᴴ) : h.PosSemidef := by
  rw [heq]
  exact (Matrix.PosSemidef.diagonal (fun k => Complex.zero_le_real.mpr (hd k))).mul_mul_conjTranspose_same l

set_option maxHeartbeats 4000000 in
-- Twelve LDL identities involve exact arithmetic on large rational coefficients.
private lemma first_signed_certificate (j : Fin 3) (ε δ : Bool) :
    ((71/250 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      ((if ε then 1 else -1 : ℝ) • e 0 + (if δ then 1 else -1 : ℝ) • f j)).PosSemidef := by
  fin_cases j <;> cases ε <;> cases δ
  · refine psd_of_ldl !![1, 0, 0; (-28639451986240/191306506793507), 1, 0; 0, 0, 1]
      ![(573919520380521/2017963723050250), (11150428315863836927/40222193053334846750), (71/250)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (-78470055713760/199343784041507), 1, 0; 0, 0, 1]
      ![(598031352124521/2017963723050250), (9460590774471836927/41912030594726846750), (71/250)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (235410167141280/548172042568021), 1, 0; 0, 0, 1]
      ![(548172042568021/2017963723050250), (28381772323415510781/115253171949926415250), (71/250)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (85918355958720/572283874312021), 1, 0; 0, 0, 1]
      ![(572283874312021/2017963723050250), (33451284947591510781/120322684574102415250), (71/250)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (-4025353104975752160/10439320279874268587), 1, 0; (1045722718275833000/10439320279874268587), (-27587497896505259570338416000/26249276065639158759538287887), 1]
      ![(31317960839622805761/105824035600478160250), (26249276065639158759538287887/115101025006045390613624786750), (10024790652795808892664569475833857/344134571539545781127236838770541750)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (-1591576588319947840/10046771621804700587), 1, 0; (-1045722718275833000/10046771621804700587), (27296154895949543027785296000/30577407754027120565890287887), 1]
      ![(30140314865414101761/105824035600478160250), (30577407754027120565890287887/110772893317657428807272786750), (24430143215575433783372625267833857/400877460007234057398963146770541750)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (4774729764959843520/29967737355657493261), 1, 0; (3137168154827499000/29967737355657493261), (-28177326066668547731638416000/30577407754027120565890287887), 1]
      ![(29967737355657493261/105824035600478160250), (91732223262081361697670863661/330415888608954275512046235250), (18096618917794269320724603447833857/400877460007234057398963146770541750)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (12076059314927256480/28790091381448789261), 1, 0; (-3137168154827499000/28790091381448789261), (27885983066112831189085296000/26249276065639158759538287887), 1]
      ![(28790091381448789261/105824035600478160250), (78747828196917476278614863661/317431493543790390092990235250), (272010830926953289092116295833857/344134571539545781127236838770541750)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (-2898159933357386000/10257513049885884587), 1, 0; (-1045722718275833000/10257513049885884587), (27452563633405188194837856000/28726148232820319719590236687), 1]
      ![(30772539149657653761/105824035600478160250), (28726148232820319719590236687/113096469348766057880048786750), (18455149261540115151851907174310657/376606984869332596603757900525741750)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (-2718769759938314000/10228578851793084587), 1, 0; (1045722718275833000/10228578851793084587), (-27431089159049614403285856000/29045168606649616058790236687), 1]
      ![(30685736555379253761/105824035600478160250), (29045168606649616058790236687/112777448974936761540848786750), (19516947120429299435682070374310657/380789421725328128934754700525741750)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (8156309279814942000/29422315665692341261), 1, 0; (-3137168154827499000/29422315665692341261), (28042391803568476356137856000/29045168606649616058790236687), 1]
      ![(29422315665692341261/105824035600478160250), (87135505819948848176370710061/324402221637116277311318235250), (11599809268817836300744760874310657/380789421725328128934754700525741750)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · refine psd_of_ldl !![1, 0, 0; (8694479800072158000/29335513071413941261), 1, 0; (3137168154827499000/29335513071413941261), (-28020917329212902564585856000/28726148232820319719590236687), 1]
      ![(29335513071413941261/105824035600478160250), (86178444698460959158770710061/323445160515628388293718235250), (10285982993501558220568741674310657/376606984869332596603757900525741750)] ?_ ?_
    · intro k; fin_cases k <;> norm_num
    · ext k l
      fin_cases k <;> fin_cases l <;>
        norm_num [e_table, f_table, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.vecMul_diagonal, map_ofNat, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]

private lemma signed_certificate (i j : Fin 3) (ε δ : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ((71/250 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (ε • e i + δ • f j)).PosSemidef := by
  have hfirst (α β : ℝ) (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1) :
      ((71/250 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
        (α • e 0 + β • f j)).PosSemidef := by
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
    · exact first_signed_certificate j true true
    · exact first_signed_certificate j true false
    · exact first_signed_certificate j false true
    · exact first_signed_certificate j false false
  have he : e 1 = -e 0 := by
    rw [e_table, e_table]
    ext k l
    fin_cases k <;> fin_cases l <;> norm_num
  have hz : e 2 = 0 := by
    rw [e_table]
    ext k l
    fin_cases k <;> fin_cases l <;> norm_num
  fin_cases i
  · exact hfirst ε δ hε hδ
  · change ((71/250 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (ε • e 1 + δ • f j)).PosSemidef
    rw [he, smul_neg, ← neg_smul]
    exact hfirst (-ε) δ (by rcases hε with rfl | rfl <;> norm_num) hδ
  · change ((71/250 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (ε • e 2 + δ • f j)).PosSemidef
    rw [hz, smul_zero, zero_add]
    have hp := (hfirst 1 δ (Or.inl rfl) hδ).add (hfirst (-1) δ (Or.inr rfl) hδ)
    have hh := hp.smul (by norm_num : (0 : ℝ) ≤ 1/2)
    convert hh using 1
    module

private lemma signed_expectation (ρ : Matrix (Fin 3) (Fin 3) ℂ) (hρ : IsDensity ρ)
    (i j : Fin 3) (ε δ : ℝ) (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ε * (trace (ρ * e i)).re + δ * (trace (ρ * f j)).re ≤ 71/250 := by
  have hn := RHLinalg.trace_mul_nonneg_of_posSemidef hρ.1
    (signed_certificate i j ε δ hε hδ)
  simp only [Matrix.mul_sub, Matrix.mul_add, mul_smul_comm, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, hρ.2] at hn
  change 0 ≤ ((71/250 : ℝ) • (1 : ℂ) -
    (ε • trace (ρ * e i) + δ • trace (ρ * f j))).re at hn
  simp only [Complex.sub_re, Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul] at hn
  linarith

private lemma state_overall_bound (ρ : Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : IsDensity ρ) : errorAt ρ 1 c + disturbanceAt ρ c b ≤ 71/250 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3,
      |(trace (ρ * e i)).re| = errorAt ρ 1 c := exists_eq_ciSup_of_finite
  obtain ⟨j, hj⟩ : ∃ j : Fin 3,
      |(trace (ρ * f j)).re| = disturbanceAt ρ c b := exists_eq_ciSup_of_finite
  rw [← hi, ← hj]
  by_cases hx : 0 ≤ (trace (ρ * e i)).re <;>
    by_cases hy : 0 ≤ (trace (ρ * f j)).re
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    simpa using signed_expectation ρ hρ i j 1 1 (Or.inl rfl) (Or.inl rfl)
  · rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge hy)]
    simpa using signed_expectation ρ hρ i j 1 (-1) (Or.inl rfl) (Or.inr rfl)
  · rw [abs_of_neg (lt_of_not_ge hx), abs_of_nonneg hy]
    simpa using signed_expectation ρ hρ i j (-1) 1 (Or.inr rfl) (Or.inl rfl)
  · rw [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge hy)]
    simpa using signed_expectation ρ hρ i j (-1) (-1) (Or.inr rfl) (Or.inr rfl)

private lemma trace_three (h : Matrix (Fin 3) (Fin 3) ℂ) :
    trace h = h 0 0 + h 1 1 + h 2 2 := by
  change (∑ k : Fin 3, h k k) = _
  simp only [Fin.sum_univ_three]

private def pure (x : Fin 3 → ℂ) (n : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1/n : ℝ) • D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity x

private lemma pure_apply (x : Fin 3 → ℂ) (n : ℝ) (i j : Fin 3) :
    pure x n i j = (1/n : ℝ) • (x i * star (x j)) := rfl

private lemma pure_isDensity (x : Fin 3 → ℂ) (n : ℝ) (hn : 0 < n)
    (ht : ∑ k, x k * star (x k) = (n : ℂ)) : IsDensity (pure x n) := by
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star x).smul (by positivity : (0 : ℝ) ≤ 1/n)
  · rw [pure, Matrix.trace_smul]
    change (1/n : ℝ) • (∑ k, x k * star (x k)) = (1 : ℂ)
    rw [ht]
    apply Complex.ext <;> simp [hn.ne']

private lemma density_exists : ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ, IsDensity ρ := by
  exact ⟨pure ![1, 0, 0] 1, pure_isDensity _ _ (by norm_num)
    (by norm_num [Fin.sum_univ_three, map_ofNat])⟩

private lemma overall_bound : overallError 1 c b ≤ 71/250 := by
  obtain ⟨ρ, hρ⟩ := density_exists
  unfold overallError
  refine csSup_le ?_ ?_
  · exact ⟨errorAt ρ 1 c + disturbanceAt ρ c b, ρ, hρ, rfl⟩
  · rintro t ⟨σ, hσ, rfl⟩
    exact state_overall_bound σ hσ

private lemma projector_psd {d : ℕ} (a : unitaryGroup (Fin d) ℂ) (i : Fin d) :
    (measurementProjector a i).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

private lemma sum_projectors {d : ℕ} (a : unitaryGroup (Fin d) ℂ) :
    ∑ i, measurementProjector a i = 1 := by
  have hh : a.val * a.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp a.property
  ext j k
  simpa only [Matrix.sum_apply, projector_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply] using congrArg (fun m => m j k) hh

private lemma projector_complement_psd {d : ℕ} (a : unitaryGroup (Fin d) ℂ) (i : Fin d) :
    (1 - measurementProjector a i).PosSemidef := by
  have heq : 1 - measurementProjector a i = ∑ k ∈ Finset.univ.erase i,
      measurementProjector a k := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), sum_projectors]
  rw [heq]
  exact Matrix.posSemidef_sum _ fun k _ => projector_psd a k

private lemma effect_difference_bound {d : ℕ} (ρ x y : Matrix (Fin d) (Fin d) ℂ)
    (hρ : IsDensity ρ) (hx : x.PosSemidef) (hy : y.PosSemidef)
    (hcx : (1 - x).PosSemidef) (hcy : (1 - y).PosSemidef) :
    |(trace (ρ * (x - y))).re| ≤ 1 := by
  have h0x := RHLinalg.trace_mul_nonneg_of_posSemidef hρ.1 hx
  have h0y := RHLinalg.trace_mul_nonneg_of_posSemidef hρ.1 hy
  have h1x := RHLinalg.trace_mul_nonneg_of_posSemidef hρ.1 hcx
  have h1y := RHLinalg.trace_mul_nonneg_of_posSemidef hρ.1 hcy
  change 0 ≤ (trace (ρ * x)).re at h0x
  change 0 ≤ (trace (ρ * y)).re at h0y
  change 0 ≤ (trace (ρ * (1 - x))).re at h1x
  change 0 ≤ (trace (ρ * (1 - y))).re at h1y
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one, hρ.2,
    Complex.sub_re, Complex.one_re] at h1x h1y
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma standard_pinch (j : Fin 3) :
    ∑ k, measurementProjector (1 : unitaryGroup (Fin 3) ℂ) k *
      measurementProjector b j * measurementProjector 1 k =
    diagonal (fun k => measurementProjector b j k k) := by
  ext k l
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [projector_apply, b, v, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_three, map_ofNat]

private lemma disturbance_bdd : BddAbove
    {t | ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ, IsDensity ρ ∧ t = disturbanceAt ρ 1 b} := by
  refine ⟨1, ?_⟩
  rintro t ⟨ρ, hρ, rfl⟩
  apply ciSup_le
  intro j
  rw [standard_pinch]
  apply effect_difference_bound ρ _ _ hρ (projector_psd b j)
  · exact Matrix.PosSemidef.diagonal fun k => (projector_psd b j).diag_nonneg
  · exact projector_complement_psd b j
  · rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro k
    change (0 : ℂ) ≤ 1 - measurementProjector b j k k
    simpa only [Matrix.sub_apply, Matrix.one_apply_eq] using
      (projector_complement_psd b j).diag_nonneg (i := k)

private lemma error_bdd (π : Equiv.Perm (Fin 3)) : BddAbove
    {t | ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ,
      IsDensity ρ ∧ t = errorAt ρ 1 (relabel b π)} := by
  refine ⟨1, ?_⟩
  rintro t ⟨ρ, hρ, rfl⟩
  apply ciSup_le
  intro i
  exact effect_difference_bound ρ _ _ hρ (projector_psd 1 i)
    (projector_psd (relabel b π) i) (projector_complement_psd 1 i)
    (projector_complement_psd (relabel b π) i)

private lemma disturbance_witness : ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ,
    IsDensity ρ ∧ (57/200 : ℝ) < disturbanceAt ρ 1 b := by
  refine ⟨pure ![-5, 11, -10] 246, pure_isDensity _ _ (by norm_num)
    (by norm_num [Fin.sum_univ_three, map_ofNat]), ?_⟩
  apply lt_of_lt_of_le _ (Finite.le_ciSup _ (1 : Fin 3))
  rw [standard_pinch]
  have heq : (trace (pure ![-5, 11, -10] 246 *
      (measurementProjector b 1 - diagonal (fun k => measurementProjector b 1 k k)))).re =
      2577721016/9041090605 := by
    norm_num [trace_three, Matrix.mul_apply, Matrix.sub_apply, Matrix.diagonal_apply,
      pure_apply, projector_apply, b, v, Fin.sum_univ_three, map_ofNat]
  rw [heq]
  norm_num

private lemma error_witness (π : Equiv.Perm (Fin 3)) :
    ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ,
      IsDensity ρ ∧ (57/200 : ℝ) < errorAt ρ 1 (relabel b π) := by
  have hh : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hh (π 1) with h | h | h
  · refine ⟨pure ![0, 1, 0] 1, pure_isDensity _ _ (by norm_num)
      (by norm_num [Fin.sum_univ_three, map_ofNat]), ?_⟩
    apply lt_of_lt_of_le _ (Finite.le_ciSup _ (1 : Fin 3))
    norm_num [trace_three, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
      pure_apply, projector_apply, relabel, b, v, Matrix.submatrix_apply,
      Fin.sum_univ_three, map_ofNat, h]
  · refine ⟨pure ![-5, -16, -11] 402, pure_isDensity _ _ (by norm_num)
      (by norm_num [Fin.sum_univ_three, map_ofNat]), ?_⟩
    apply lt_of_lt_of_le _ (Finite.le_ciSup _ (1 : Fin 3))
    norm_num [trace_three, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
      pure_apply, projector_apply, relabel, b, v, Matrix.submatrix_apply,
      Fin.sum_univ_three, map_ofNat, h]
  · refine ⟨pure ![0, 1, 0] 1, pure_isDensity _ _ (by norm_num)
      (by norm_num [Fin.sum_univ_three, map_ofNat]), ?_⟩
    apply lt_of_lt_of_le _ (Finite.le_ciSup _ (1 : Fin 3))
    norm_num [trace_three, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
      pure_apply, projector_apply, relabel, b, v, Matrix.submatrix_apply,
      Fin.sum_univ_three, map_ofNat, h]

private lemma disturbance_lower : (57/200 : ℝ) < disturbance 1 b := by
  obtain ⟨ρ, hρ, ht⟩ := disturbance_witness
  exact ht.trans_le (le_csSup disturbance_bdd ⟨ρ, hρ, rfl⟩)

private lemma relaxed_lower : (57/200 : ℝ) < relaxedError 1 b := by
  apply (Finite.lt_ciInf_iff).2
  intro π
  obtain ⟨ρ, hρ, ht⟩ := error_witness π
  exact ht.trans_le (le_csSup (error_bdd π) ⟨ρ, hρ, rfl⟩)

theorem result : ¬ claim := by
  intro h
  have hh := h 3 (by norm_num) 1 c b
  have hl := lt_min relaxed_lower disturbance_lower
  have hu := overall_bound
  linarith

end
end D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation
