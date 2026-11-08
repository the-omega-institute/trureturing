/- GID: D5/S1/Recurrence/Algebraic/A392976InverseRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/A392976InverseRecurrence
   mirror-E: none(waiver:formal-power-series-proof)
   anchors: []
   utility: none
   digest: The zero-constant quintic inverse satisfies the full A392976 recurrence and a nonzero homogeneous differential equation. -/

import D5.S1.Recurrence.A308815DFiniteRecurrence

/-! # A392976: the inverse quintic and its full differential recurrence -/

open scoped BigOperators
open PowerSeries
namespace D5.S1.Recurrence.Algebraic.A392976InverseRecurrence
noncomputable section
set_option maxRecDepth 8192

/-- The polynomial whose formal reversion defines A392976. -/
def f : Polynomial ℚ := Polynomial.X * ((1 - Polynomial.X^2)^2 - Polynomial.X)

private theorem f_zero : constantCoeff (f : PowerSeries ℚ) = 0 := by simp [f]
private theorem f_one : IsUnit (coeff 1 (f : PowerSeries ℚ)) := by
  convert isUnit_one (M := ℚ) using 1 <;> norm_num [f, Polynomial.coeff_mul]

/-- The unique zero-constant formal inverse, over the rational coefficient field. -/
def U : PowerSeries ℚ := (f : PowerSeries ℚ).substInvOfIsUnit f_one

/-- Division of the zero-constant inverse by X, expressed by its shifted coefficients. -/
def A : PowerSeries ℚ := PowerSeries.mk (fun n => coeff (n + 1) U)

/-- The offset-zero coefficients of U/X. -/
def a (n : ℕ) : ℚ := coeff (n + 1) U

/-- Homogeneous D-finiteness over Q, with a nonzero polynomial differential operator. -/
def DFinite (B : PowerSeries ℚ) : Prop :=
  ∃ (d : ℕ) (p : Fin (d + 1) → Polynomial ℚ),
    (∃ j, p j ≠ 0) ∧
    ∑ j : Fin (d + 1), (p j : PowerSeries ℚ) *
      (derivative (R := ℚ))^[j.val] B = 0

private def H : Polynomial ℚ := Polynomial.derivative f
private def theta (B : PowerSeries ℚ) : PowerSeries ℚ := X * derivative (R := ℚ) B
private def op (w : ℕ → ℕ → ℚ) (B : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.range 6, X^k *
    ∑ j ∈ Finset.range 6, C (w k j) * theta^[j] B

private def wA : ℕ → ℕ → ℚ
  | 0, 1 => -100965943384944
  | 0, 2 => 97473596443030
  | 0, 3 => 77470631009665
  | 0, 4 => -97473596443030
  | 0, 5 => 23495312375279
  | 1, 1 => 118367263850820
  | 1, 2 => -124300362766572
  | 1, 3 => -45186542426046
  | 1, 4 => 124300362766572
  | 1, 5 => -73180721424774
  | 2, 1 => 256878621904608
  | 2, 2 => 120126524084718
  | 2, 3 => -1087431887019138
  | 2, 4 => -1357425767727510
  | 2, 5 => -406745978528262
  | 3, 0 => -826722892323288
  | 3, 1 => -4947003142661262
  | 3, 2 => -10570826234814934
  | 3, 3 => -9944541215764618
  | 3, 4 => -3878329947176378
  | 3, 5 => -384334715888720
  | 4, 0 => -3941533408005120
  | 4, 1 => -13053923098507960
  | 4, 2 => -15561682530242400
  | 4, 3 => -7815804403003375
  | 4, 4 => -1265812196415000
  | 4, 5 => 78200611484375
  | 5, 0 => 702108258284160
  | 5, 1 => 2705579300780400
  | 5, 2 => 4039257006377500
  | 5, 3 => 2926813222793750
  | 5, 4 => 1029928976337500
  | 5, 5 => 140685548031250
  | _, _ => 0

private def wU : ℕ → ℕ → ℚ
  | 0, 1 => 443869704406506
  | 0, 2 => -954732998996935
  | 0, 3 => 702318140534575
  | 0, 4 => -214950158319425
  | 0, 5 => 23495312375279
  | 1, 1 => -631696696084332
  | 1, 2 => 1488868655358738
  | 1, 3 => -1274195207740074
  | 1, 4 => 490203969890442
  | 1, 5 => -73180721424774
  | 2, 1 => 150303090946488
  | 2, 2 => -694672635940308
  | 2, 3 => 274811398608282
  | 2, 4 => 676304124913800
  | 2, 5 => -406745978528262
  | 3, 1 => -47328111063336
  | 3, 2 => -163835111692148
  | 3, 3 => 1725431414053694
  | 3, 4 => -1956656367732778
  | 3, 5 => -384334715888720
  | 4, 0 => 22498755364440
  | 4, 1 => 76280596048590
  | 4, 2 => -491148614566025
  | 4, 3 => -1970549502499625
  | 4, 4 => -1656815253836875
  | 4, 5 => 78200611484375
  | 5, 0 => -1783830606240
  | 5, 1 => -8783208787100
  | 5, 2 => 31535715708750
  | 5, 3 => 213952797756250
  | 5, 4 => 326501236181250
  | 5, 5 => 140685548031250
  | _, _ => 0

set_option maxHeartbeats 4000000 in
private def num : ℕ → Polynomial ℚ
  | 0 => (1) * Polynomial.X^1
  | 1 => (1) * Polynomial.X^1 +
      (-1) * Polynomial.X^2 +
      (-2) * Polynomial.X^3 +
      (1) * Polynomial.X^5
  | 2 => (1) * Polynomial.X^1 +
      (-3) * Polynomial.X^2 +
      (2) * Polynomial.X^3 +
      (10) * Polynomial.X^4 +
      (-9) * Polynomial.X^5 +
      (-18) * Polynomial.X^6 +
      (-12) * Polynomial.X^7 +
      (12) * Polynomial.X^8 +
      (23) * Polynomial.X^9 +
      (-3) * Polynomial.X^10 +
      (-18) * Polynomial.X^11 +
      (5) * Polynomial.X^13
  | 3 => (1) * Polynomial.X^1 +
      (-3) * Polynomial.X^2 +
      (30) * Polynomial.X^3 +
      (-58) * Polynomial.X^4 +
      (-111) * Polynomial.X^5 +
      (344) * Polynomial.X^6 +
      (-120) * Polynomial.X^7 +
      (-516) * Polynomial.X^8 +
      (838) * Polynomial.X^9 +
      (230) * Polynomial.X^10 +
      (-1428) * Polynomial.X^11 +
      (2) * Polynomial.X^12 +
      (1154) * Polynomial.X^13 +
      (-480) * Polynomial.X^14 +
      (-840) * Polynomial.X^15 +
      (380) * Polynomial.X^16 +
      (525) * Polynomial.X^17 +
      (-95) * Polynomial.X^18 +
      (-170) * Polynomial.X^19 +
      (25) * Polynomial.X^21
  | 4 => (1) * Polynomial.X^1 +
      (1) * Polynomial.X^2 +
      (122) * Polynomial.X^3 +
      (-386) * Polynomial.X^4 +
      (499) * Polynomial.X^5 +
      (266) * Polynomial.X^6 +
      (-8516) * Polynomial.X^7 +
      (15908) * Polynomial.X^8 +
      (22865) * Polynomial.X^9 +
      (-69729) * Polynomial.X^10 +
      (-11518) * Polynomial.X^11 +
      (131900) * Polynomial.X^12 +
      (-43505) * Polynomial.X^13 +
      (-145076) * Polynomial.X^14 +
      (116152) * Polynomial.X^15 +
      (116328) * Polynomial.X^16 +
      (-150549) * Polynomial.X^17 +
      (-104313) * Polynomial.X^18 +
      (80558) * Polynomial.X^19 +
      (65030) * Polynomial.X^20 +
      (-10895) * Polynomial.X^21 +
      (-18710) * Polynomial.X^22 +
      (-6420) * Polynomial.X^23 +
      (2220) * Polynomial.X^24 +
      (3555) * Polynomial.X^25 +
      (25) * Polynomial.X^26 +
      (-1050) * Polynomial.X^27 +
      (125) * Polynomial.X^29
  | 5 => (1) * Polynomial.X^1 +
      (13) * Polynomial.X^2 +
      (438) * Polynomial.X^3 +
      (-978) * Polynomial.X^4 +
      (7685) * Polynomial.X^5 +
      (-26788) * Polynomial.X^6 +
      (-43424) * Polynomial.X^7 +
      (272636) * Polynomial.X^8 +
      (-324576) * Polynomial.X^9 +
      (-396636) * Polynomial.X^10 +
      (2551920) * Polynomial.X^11 +
      (-2784162) * Polynomial.X^12 +
      (-6659412) * Polynomial.X^13 +
      (13546852) * Polynomial.X^14 +
      (8541872) * Polynomial.X^15 +
      (-29328692) * Polynomial.X^16 +
      (-4784842) * Polynomial.X^17 +
      (39427778) * Polynomial.X^18 +
      (-2241348) * Polynomial.X^19 +
      (-34429094) * Polynomial.X^20 +
      (8994586) * Polynomial.X^21 +
      (18934780) * Polynomial.X^22 +
      (-14424160) * Polynomial.X^23 +
      (-9335500) * Polynomial.X^24 +
      (11637440) * Polynomial.X^25 +
      (5216180) * Polynomial.X^26 +
      (-4640880) * Polynomial.X^27 +
      (-1946710) * Polynomial.X^28 +
      (984660) * Polynomial.X^29 +
      (271220) * Polynomial.X^30 +
      (-168080) * Polynomial.X^31 +
      (13300) * Polynomial.X^32 +
      (44825) * Polynomial.X^33 +
      (-6375) * Polynomial.X^34 +
      (-7250) * Polynomial.X^35 +
      (625) * Polynomial.X^37
  | _ => 0

set_option maxHeartbeats 4000000 in
private theorem num_recurrence (j : ℕ) (hj : j < 4) :
    num (j + 2) = f * (H * Polynomial.derivative (num (j + 1)) -
      (2*j+1 : ℕ) * (Polynomial.derivative H * num (j + 1))) := by
  have hs : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl <;> norm_num [num, H, f, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_smul, smul_eq_mul] <;> ring

private theorem inverse_right : (f : PowerSeries ℚ).subst U = X :=
  PowerSeries.subst_substInvOfIsUnit_right _ f_zero _

private theorem inverse_left : U.subst (f : PowerSeries ℚ) = X :=
  PowerSeries.subst_substInvOfIsUnit_left _ f_zero _

private theorem X_A : X * A = U := by
  ext n
  cases n with
  | zero => simp [U]
  | succ n => simp [A, coeff_succ_X_mul]

private theorem theta_transport (B : PowerSeries ℚ) :
    (H : PowerSeries ℚ) * (theta B).subst (f : PowerSeries ℚ) =
      (f : PowerSeries ℚ) * derivative (R := ℚ) (B.subst (f : PowerSeries ℚ)) := by
  have hf : HasSubst (f : PowerSeries ℚ) := .of_constantCoeff_zero f_zero
  rw [theta, subst_mul hf, subst_X hf, derivative_subst hf]
  rw [derivative_coe]
  dsimp [H]
  ring

private theorem coe_nat (n : ℕ) : ((n : Polynomial ℚ) : PowerSeries ℚ) = n :=
  Polynomial.coeToPowerSeries.ringHom.map_natCast n

private theorem scaled_step (B : PowerSeries ℚ) (d : ℕ) (N : Polynomial ℚ)
    (h : (H : PowerSeries ℚ)^(d + 1) * B.subst (f : PowerSeries ℚ) = N) :
    (H : PowerSeries ℚ)^(d + 3) * (theta B).subst (f : PowerSeries ℚ) =
      (f * (H * Polynomial.derivative N -
        (d + 1 : ℕ) * (Polynomial.derivative H * N)) : Polynomial ℚ) := by
  have hd := congrArg (derivative (R := ℚ)) h
  simp only [Derivation.leibniz, derivative_pow, derivative_coe,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, smul_eq_mul] at hd
  simp only [Polynomial.coe_mul, Polynomial.coe_sub, coe_nat]
  linear_combination (H : PowerSeries ℚ)^(d + 2) * theta_transport B +
    (f : PowerSeries ℚ) * H * hd -
    (f : PowerSeries ℚ) * (d + 1 : PowerSeries ℚ) * (Polynomial.derivative H : PowerSeries ℚ) * h

private theorem scaled_iterates (j : ℕ) (hj : j < 5) :
    (H : PowerSeries ℚ)^(2*j + 1) *
      (theta^[j + 1] U).subst (f : PowerSeries ℚ) = (num (j + 1) : Polynomial ℚ) := by
  induction j with
  | zero =>
    simpa [Function.iterate_one, inverse_left, num, f] using theta_transport U
  | succ j ih =>
    have h := scaled_step (theta^[j + 1] U) (2*j) (num (j + 1)) (ih (by omega))
    rw [num_recurrence j (by omega)]
    convert h using 1 <;>
      simp only [Function.iterate_succ_apply', Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] <;>
      congr 1 <;> omega

set_option maxHeartbeats 4000000 in
private theorem polynomial_certificate :
    (∑ k ∈ Finset.range 6, f^k *
      ∑ j ∈ Finset.range 6,
        Polynomial.C (wU k j) * num j * H^(if j = 0 then 9 else 10 - 2*j)) = 0 := by
  norm_num [Finset.sum_range_succ, wU, num, H, f, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_smul, smul_eq_mul]
  ring

private theorem common_denominator (j : ℕ) (hj : j < 6) :
    (H : PowerSeries ℚ)^9 * (theta^[j] U).subst (f : PowerSeries ℚ) =
      (num j : Polynomial ℚ) * (H : PowerSeries ℚ)^(if j = 0 then 9 else 10 - 2*j) := by
  cases j with
  | zero => simp [num, inverse_left, mul_comm]
  | succ j =>
    have he : 8 - 2*j + (2*j + 1) = 9 := by omega
    have hexp : 10 - 2*(j+1) = 8 - 2*j := by omega
    simp only [Nat.succ_ne_zero, ↓reduceIte, hexp]
    calc
      _ = (H : PowerSeries ℚ)^(8 - 2*j) *
          ((H : PowerSeries ℚ)^(2*j + 1) * (theta^[j+1] U).subst (f : PowerSeries ℚ)) := by
        rw [← mul_assoc, ← pow_add, he]
      _ = _ := by rw [scaled_iterates j (by omega)]; ring

private theorem inverse_operator : op wU U = 0 := by
  have hf : HasSubst (f : PowerSeries ℚ) := .of_constantCoeff_zero f_zero
  have hu : HasSubst U := .of_constantCoeff_zero (PowerSeries.constantCoeff_substInvOfIsUnit _ _)
  have hcert := congrArg Polynomial.coeToPowerSeries.ringHom polynomial_certificate
  have hscaled : (H : PowerSeries ℚ)^9 * (op wU U).subst (f : PowerSeries ℚ) = 0 := by
    calc
      _ = ∑ k ∈ Finset.range 6, (f : PowerSeries ℚ)^k *
          ∑ j ∈ Finset.range 6, C (wU k j) *
            ((H : PowerSeries ℚ)^9 * (theta^[j] U).subst (f : PowerSeries ℚ)) := by
        simp only [op, ← coe_substAlgHom hf, map_sum, map_mul, map_pow,
          substAlgHom_X, ← algebraMap_eq, AlgHom.commutes]
        simp only [algebraMap_eq, coe_substAlgHom]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ k ∈ Finset.range 6, (f : PowerSeries ℚ)^k *
          ∑ j ∈ Finset.range 6, C (wU k j) *
            ((num j : Polynomial ℚ) * (H : PowerSeries ℚ)^(if j = 0 then 9 else 10 - 2*j)) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [common_denominator j (Finset.mem_range.mp hj)]
      _ = 0 := by simpa only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
          Polynomial.coe_C, mul_assoc] using hcert
  have hh : (H : PowerSeries ℚ) ≠ 0 := by
    intro h
    have hz := congrArg constantCoeff h
    norm_num [H, f] at hz
  have hz : (op wU U).subst (f : PowerSeries ℚ) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero _ hh)
  have h := congrArg (fun B : PowerSeries ℚ => B.subst U) hz
  simpa only [subst_comp_subst_apply hf hu, inverse_right, X_subst, ← coe_substAlgHom hu, map_zero] using h

set_option maxHeartbeats 4000000 in
private theorem operator_shift (B : PowerSeries ℚ) : op wU (X * B) = X * op wA B := by
  norm_num [op, wU, wA, Finset.sum_range_succ, Function.iterate_succ_apply',
    theta, Derivation.leibniz, derivative_X, derivative_one, map_add, map_mul,
    map_natCast, map_ofNat]
  ring

private theorem A_operator : op wA A = 0 := by
  apply X_mul_cancel
  rw [mul_zero, ← operator_shift, X_A, inverse_operator]

private theorem coeff_theta_iterate (B : PowerSeries ℚ) (j n : ℕ) :
    coeff n (theta^[j] B) = (n : ℚ)^j * coeff n B := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', theta,
      D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff, ih, pow_succ]
    ring

private theorem coeff_op (w : ℕ → ℕ → ℚ) (B : PowerSeries ℚ) (n : ℕ) (hn : 5 ≤ n) :
    coeff n (op w B) = ∑ k ∈ Finset.range 6,
      ∑ j ∈ Finset.range 6, w k j * ((n-k : ℕ) : ℚ)^j * coeff (n-k) B := by
  simp only [op, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_X_pow_mul', if_pos (by have := Finset.mem_range.mp hk; omega)]
  simp only [map_sum, coeff_C_mul, coeff_theta_iterate, mul_assoc]

private theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    283*(n : ℚ)*(n-1)*(n-2)*(83022305213*n-178385058984)*(n+1)*a n -
    6*n*(n-1)*(n-2)*(12196786904129*n^2-45110300936020*n+52641391340361)*a (n-1) -
    6*(n-1)*(n-2)*(67790996421377*n^3-248299346995054*n^2+202497447227007*n+3061418504418)*a (n-2) -
    2*(n-2)*(192167357944360*n^4-559010679688491*n^3-2120668219560541*n^2+9123363136130610*n-8342981628089220)*a (n-3) +
    5*(15640122296875*n^5-565964885220500*n^4+4989857715427325*n^3-18667678380008380*n^2+32085126156301848*n-20925325629575136)*a (n-4) +
    10*(5*n-17)*(5*n-18)*(5*n-21)*(5*n-19)*(22509687685*n-60308240636)*a (n-5) = 0 := by
  have h := congrArg (coeff n) A_operator
  rw [coeff_op wA A n hn] at h
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  norm_num [Finset.sum_range_succ, wA, Nat.cast_sub h1, Nat.cast_sub h2,
    Nat.cast_sub h3, Nat.cast_sub h4, Nat.cast_sub hn, A, a] at h ⊢
  linear_combination h

private def p : ℕ → Polynomial ℚ
  | 0 => (-826722892323288) * Polynomial.X^3 + (-3941533408005120) * Polynomial.X^4 + (702108258284160) * Polynomial.X^5
  | 1 => (-2474598487285584) * Polynomial.X^3 + (-29725035256305912) * Polynomial.X^4 + (-37619021616684360) * Polynomial.X^5 + (10842264054320400) * Polynomial.X^6
  | 2 => (-487468272050316) * Polynomial.X^3 + (-18745339188989196) * Polynomial.X^4 + (-73317780250674234) * Polynomial.X^5 + (-46696771941891900) * Polynomial.X^6 + (22139482729590000) * Polynomial.X^7
  | 3 => (80011861733460) * Polynomial.X^3 + (-1128902401445964) * Polynomial.X^4 + (-19400635956590748) * Polynomial.X^5 + (-42822888796040886) * Polynomial.X^6 + (-13455662294384000) * Polynomial.X^7 + (12623525781600000) * Polynomial.X^8
  | 4 => (137479527309760) * Polynomial.X^4 + (-607506851481168) * Polynomial.X^5 + (-5424885553010130) * Polynomial.X^6 + (-7721677106063578) * Polynomial.X^7 + (-483806081571250) * Polynomial.X^8 + (2436784456650000) * Polynomial.X^9
  | 5 => (23495312375279) * Polynomial.X^5 + (-73180721424774) * Polynomial.X^6 + (-406745978528262) * Polynomial.X^7 + (-384334715888720) * Polynomial.X^8 + (78200611484375) * Polynomial.X^9 + (140685548031250) * Polynomial.X^10
  | _ => 0

set_option maxHeartbeats 4000000 in
private theorem normal_form (B : PowerSeries ℚ) :
    op wA B = ∑ j : Fin 6, (p j.val : PowerSeries ℚ) * (derivative (R := ℚ))^[j.val] B := by
  norm_num [op, wA, p, Finset.sum_range_succ, Fin.sum_univ_succ,
    Function.iterate_succ_apply', theta, Derivation.leibniz, derivative_pow,
    derivative_X, derivative_one, map_add, map_mul, map_natCast, map_ofNat,
    Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_neg, coe_nat]
  ring

private theorem dfinite : DFinite A := by
  refine ⟨5, fun j => p j.val, ?_, ?_⟩
  · refine ⟨⟨5, by decide⟩, ?_⟩
    intro hz
    change p 5 = 0 at hz
    have h := congrArg (Polynomial.coeff 5) hz
    norm_num [p] at h
  · exact (normal_form A).symm.trans A_operator

/-- Both inverse compositions, uniqueness, the quotient coefficients, D-finiteness,
and the exact six-term recurrence at every natural index at least five. -/
def claim : Prop :=
  constantCoeff U = 0 ∧
  (f : PowerSeries ℚ).subst U = X ∧
  U.subst (f : PowerSeries ℚ) = X ∧
  (∀ V : PowerSeries ℚ, constantCoeff V = 0 →
    (f : PowerSeries ℚ).subst V = X → V = U) ∧
  X * A = U ∧ DFinite A ∧ ∀ n : ℕ, 5 ≤ n →
    283*(n : ℚ)*(n-1)*(n-2)*(83022305213*n-178385058984)*(n+1)*a n -
    6*n*(n-1)*(n-2)*(12196786904129*n^2-45110300936020*n+52641391340361)*a (n-1) -
    6*(n-1)*(n-2)*(67790996421377*n^3-248299346995054*n^2+202497447227007*n+3061418504418)*a (n-2) -
    2*(n-2)*(192167357944360*n^4-559010679688491*n^3-2120668219560541*n^2+9123363136130610*n-8342981628089220)*a (n-3) +
    5*(15640122296875*n^5-565964885220500*n^4+4989857715427325*n^3-18667678380008380*n^2+32085126156301848*n-20925325629575136)*a (n-4) +
    10*(5*n-17)*(5*n-18)*(5*n-21)*(5*n-19)*(22509687685*n-60308240636)*a (n-5) = 0

/-- The complete A392976 assertion for the zero-constant formal inverse. -/
theorem result : claim := by
  refine ⟨PowerSeries.constantCoeff_substInvOfIsUnit _ _, inverse_right, inverse_left,
    ?_, X_A, dfinite, recurrence⟩
  intro V hV hv
  exact PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X _ f_zero f_one
    (.of_constantCoeff_zero hV) hv

end
end D5.S1.Recurrence.Algebraic.A392976InverseRecurrence
