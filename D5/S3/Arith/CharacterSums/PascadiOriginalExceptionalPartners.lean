/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalExceptionalPartners
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalExceptionalPartners
   mirror-E: none(waiver:open-total-original-count)
   anchors: []
   utility: none
   digest: Integer divisor values count the original zero-polynomial partners. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalSingularPartners
import D5.S3.Arith.CharacterSums.PascadiOriginalLinearFibers
import D5.S3.Arith.CharacterSums.PascadiModularZeroPartners

/-! The zero polynomial and the nonzero content-p pencil are distinct strata.
The zero-polynomial count below uses actual integer values and physical points;
it does not assume that the fixed original baseline is nonaligned. -/

open Polynomial

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem literal_integer_eq_of_residue {c : ℕ} {X : ℝ} {u v : ℤ}
    (hu : |(u : ℝ)| ≤ X) (hv : |(v : ℝ)| ≤ X)
    (hsmall : 2*X < c) (heq : (u : ZMod c) = v) : u = v := by
  have hm : ((u-v : ℤ) : ZMod c) = 0 := by
    simpa only [Int.cast_sub] using sub_eq_zero.mpr heq
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hm
  apply sub_eq_zero.mp
  by_contra hn
  have hle := Int.le_abs_of_dvd hn hd
  have hleR : (c : ℝ) ≤ |((u-v : ℤ) : ℝ)| := by exact_mod_cast hle
  have hlt : |((u-v : ℤ) : ℝ)| < c := by
    push_cast
    exact (abs_sub (u : ℝ) (v : ℝ)).trans_lt (by linarith)
  exact (not_le_of_gt hlt) hleR

private theorem actual_coordinate_of_linear_residue {c m : ℕ} [NeZero c]
    {t w : ℤ} {X Y : ℝ} (B : MiddleBasis c t w)
    (hr : IsUnit (B.R.1 : ZMod c)) (hw : IsUnit (w : ZMod c))
    (f : ZMod c →+* ZMod m) (hXsmall : 2*X < m) (hYsmall : 2*Y < c)
    (x y : Coordinate) (hx : physical B.R B.V x ∈ literalBox X Y)
    (hy : physical B.R B.V y ∈ literalBox X Y)
    (hlinear : (x.1 : ZMod m) +
        f ((B.V.1 : ZMod c)*(↑hr.unit⁻¹ : ZMod c))*x.2 =
      (y.1 : ZMod m) + f ((B.V.1 : ZMod c)*(↑hr.unit⁻¹ : ZMod c))*y.2) : x = y := by
  let β : ZMod c := (B.V.1 : ZMod c)*(↑hr.unit⁻¹ : ZMod c)
  have hphys (z : Coordinate) : ((physical B.R B.V z).1 : ZMod c) =
      (hr.unit : ZMod c)*((z.1 : ZMod c)+β*z.2) := by
    have hinv : (↑hr.unit⁻¹ : ZMod c)*(hr.unit : ZMod c) = 1 := by simp
    simp only [physical, Int.cast_add, Int.cast_mul, β]
    linear_combination -(B.V.1 : ZMod c)*(z.2 : ZMod c)*hinv -
      (z.1 : ZMod c)*hr.unit_spec
  have hfirstmod : ((physical B.R B.V x).1 : ZMod m) =
      ((physical B.R B.V y).1 : ZMod m) := by
    have hx' := congrArg f (hphys x)
    have hy' := congrArg f (hphys y)
    simp only [map_intCast, map_mul, map_add] at hx' hy'
    rw [hx', hy']
    exact congrArg (fun a : ZMod m => f ↑hr.unit*a) hlinear
  have hfirst := literal_integer_eq_of_residue hx.1 hy.1 hXsmall hfirstmod
  have hsecondmod : ((physical B.R B.V x).2 : ZMod c) =
      ((physical B.R B.V y).2 : ZMod c) := by
    apply hw.mul_left_cancel
    have hm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (B.physical_mem x)
    have hm' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (B.physical_mem y)
    push_cast at hm hm'
    rw [hfirst] at hm
    linear_combination hm-hm'
  apply B.coordinates_unique (Nat.pos_of_ne_zero (NeZero.ne c))
  exact Prod.ext hfirst (literal_integer_eq_of_residue hx.2 hy.2 hYsmall hsecondmod)

private theorem original_coordinate_height (p : ℕ) (hp : p.Prime) (J₁ J₂ M : ℝ)
    (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂)
    (hcap : (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3)
    (hlarge : (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ)) : J₁ ≤ p := by
  let A : ℝ := (24*(8*(18 : ℝ))^4)^5
  have hA : 1 ≤ A := by norm_num [A]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hJ₁ : 0 ≤ J₁ := by linarith
  have hJ₂ : 0 ≤ J₂ := by linarith
  have h40 : J₁^40 ≤ M^40*(p : ℝ)^24 := by
    calc
      _ ≤ (J₁*J₂)^40 := pow_le_pow_left₀ hJ₁ (le_mul_of_one_le_right hJ₁ h₂) 40
      _ ≤ _ := by
        convert pow_le_pow_left₀ (by positivity : 0 ≤ (J₁*J₂)^5) hcap 8 using 1 <;> ring
  have hbound : J₁^40 < (p : ℝ)^25 := by
    calc
      _ ≤ A*J₁^40 := le_mul_of_one_le_left (by positivity) hA
      _ ≤ A*(M^40*(p : ℝ)^24) := mul_le_mul_of_nonneg_left h40 (by linarith)
      _ = (A*M^40)*(p : ℝ)^24 := by ring
      _ < (p : ℝ)*(p : ℝ)^24 := mul_lt_mul_of_pos_right hlarge (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ hJ₁ hp0.le (by decide : 40 ≠ 0)).mp
    (hbound.le.trans (pow_le_pow_right₀ hp1 (by decide : 25 ≤ 40)))

private theorem integer_linear_height (p : ℝ) (hp : 2 ≤ p) (b : ℤ)
    (hb : |(b : ℝ)| ≤ p^3) (z : Coordinate) (hz : CoordinateBound p p z) :
    |(((coordinateLinear z).eval b : ℤ) : ℝ)| ≤ 2*p^4 := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hpp : p ≤ p^4 := by simpa using pow_le_pow_right₀ hp1 (by decide : 1 ≤ 4)
  simp only [coordinateLinear, PrimeCube.linear, eval_add, eval_mul, eval_C, eval_X,
    Int.cast_add, Int.cast_mul]
  calc
    _ ≤ |(z.1 : ℝ)|+|(z.2 : ℝ)| * |(b : ℝ)| := by
      simpa only [abs_mul] using abs_add_le (z.1 : ℝ) ((z.2 : ℝ)*b)
    _ ≤ p+p*p^3 := add_le_add hz.1 (mul_le_mul hz.2 hb (abs_nonneg _) hp0)
    _ ≤ _ := by nlinarith

private theorem integer_singular_value_height (p : ℝ) (hp : 2 ≤ p) (b : ℤ)
    (hb : |(b : ℝ)| ≤ p^3) (q : Coordinate) (base : Endpoint) (x : Coordinate)
    (hq : CoordinateBound p p q) (h₁ : CoordinateBound p p base.1)
    (h₂ : CoordinateBound p p base.2) (hx : CoordinateBound p p x) :
    |(((singularValuePolynomial q base x).eval b : ℤ) : ℝ)| ≤ p^12 := by
  have hp0 : 0 ≤ p := by linarith
  have hlq := integer_linear_height p hp b hb q hq
  have hl₁ := integer_linear_height p hp b hb base.1 h₁
  have hl₂ := integer_linear_height p hp b hb base.2 h₂
  have hlx := integer_linear_height p hp b hb x hx
  have hQ : (endpointQ base).eval b =
      (coordinateLinear base.1).eval b*(coordinateLinear base.2).eval b := by
    simp only [endpointQ, coordinateLinear, PrimeCube.linear, PrimeCube.quadratic,
      coeffQ, coeffR, coeffS, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  have hL : (endpointL q base).eval b =
      (coordinateLinear base.1).eval b+(coordinateLinear base.2).eval b-
        (coordinateLinear q).eval b := by
    simp only [endpointL, coordinateLinear, PrimeCube.linear, coeffL, coeffM,
      eval_add, eval_mul, eval_C, eval_X]
    ring
  have hQb : |(((endpointQ base).eval b : ℤ) : ℝ)| ≤ 4*p^8 := by
    rw [hQ, Int.cast_mul, abs_mul]
    convert mul_le_mul hl₁ hl₂ (abs_nonneg _) (by positivity) using 1 <;> ring
  have hLb : |(((endpointL q base).eval b : ℤ) : ℝ)| ≤ 6*p^4 := by
    rw [hL, Int.cast_sub, Int.cast_add]
    exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans (by linarith))
  have hp4 : (16 : ℝ) ≤ p^4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp 4
    norm_num at hh
    exact hh
  simp only [singularValuePolynomial, eval_add, eval_neg, eval_mul,
    Int.cast_add, Int.cast_neg, Int.cast_mul]
  calc
    _ ≤ |(((endpointQ base).eval b : ℤ) : ℝ)|+
        |(((endpointL q base).eval b : ℤ) : ℝ)| * |(((coordinateLinear x).eval b : ℤ) : ℝ)| := by
      simpa only [abs_neg, abs_mul] using abs_add_le
        (-(((endpointQ base).eval b : ℤ) : ℝ))
        ((((endpointL q base).eval b : ℤ) : ℝ)*(((coordinateLinear x).eval b : ℤ) : ℝ))
    _ ≤ 4*p^8+(6*p^4)*(2*p^4) :=
      add_le_add hQb (mul_le_mul hLb hlx (abs_nonneg _) (by positivity))
    _ = 16*p^8 := by ring
    _ ≤ p^4*p^8 := mul_le_mul_of_nonneg_right hp4 (by positivity)
    _ = _ := by ring

private theorem integer_singular_product (b : ℤ) (q : Coordinate) (base e : Endpoint)
    (he : pencil q base e = 0) :
    (singularValuePolynomial q base e.1).eval b *
        (singularValuePolynomial q base e.2).eval b = (singularProductPolynomial q base).eval b := by
  have hid : singularValuePolynomial q base e.1 * singularValuePolynomial q base e.2-
      singularProductPolynomial q base = endpointL q base*pencil q base e := by
    simp only [singularValuePolynomial, singularProductPolynomial, pencil,
      endpointL, endpointQ, coordinateLinear, PrimeCube.linear, PrimeCube.quadratic,
      coeffL, coeffM, coeffQ, coeffR, coeffS, map_add, map_sub, map_mul]
    ring
  rw [he, mul_zero] at hid
  have hh := congrArg (Polynomial.evalRingHom b) (sub_eq_zero.mp hid)
  simpa only [map_mul, coe_evalRingHom] using hh

/-- The identically zero integer-pencil stratum has uniformly subpower many
actual original endpoint pairs, including aligned baselines. Integer divisor
values and the two literal physical widths provide genuine point recovery.
Only the coordinate-height bound J₁ ≤ p is required; no scale cap or
large-prime cutoff is part of this interface. -/
theorem actual_zero_polynomial_partners_subpower_of_coordinate_height (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ X Y : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)))
      (hw : IsUnit (w : ZMod (p^3))),
      2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) → J₂ ≤ J₁ → 1 ≤ J₂ →
      WordSolution (p^3) a₁ a₂ B.R B.V q base →
      IsUnit ((physical B.R B.V base.1).1 : ZMod (p^3)) →
      IsUnit ((physical B.R B.V base.2).1 : ZMod (p^3)) →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q → CoordinateBound J₁ J₂ base.1 → CoordinateBound J₁ J₂ base.2 →
      (∀ e ∈ S, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (∀ e ∈ S, pencil q base e = 0) →
      J₁ ≤ (p : ℝ) →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε := by
  classical
  obtain ⟨C, hC, hdiv⟩ := signed_divisors_antidiag_subpower (ε/24) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro p hp J₁ J₂ X Y t w B a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hXsmall hYsmall h₁₂ h₂ hbase hx hy hk hq hb₁ hb₂ hbox hzero hJp
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fact (1 < p^3) := ⟨lt_of_lt_of_le (by decide : 1 < 2^3)
    (pow_le_pow_left₀ (by decide : 0 ≤ 2) hp.two_le 3)⟩
  let β := (B.V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let b : ℤ := β.val
  have hb : (b : ZMod (p^3)) = β := by simp only [b, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hbabs : |(b : ℝ)| ≤ (p : ℝ)^3 := by
    have hval := β.val_lt
    have hnonneg : (0 : ℝ) ≤ b := by dsimp only [b]; positivity
    rw [abs_of_nonneg hnonneg]
    change (β.val : ℝ) ≤ (p : ℝ)^3
    exact_mod_cast hval.le
  have hu := original_singular_unit_observations a₁ a₂ ha₁ ha₂ B.R B.V q base
    hr ht hbase hx hy hk
  have heval (P : ℤ[X]) : P.eval₂ (Int.castRingHom (ZMod (p^3))) β =
      ((P.eval b : ℤ) : ZMod (p^3)) :=
    reduce_eval_at_lift (RingHom.id (ZMod (p^3))) P β b hb
  have hLn : (endpointL q base).eval b ≠ 0 := by
    intro hz
    have hh := hu.1.ne_zero
    rw [heval, hz, Int.cast_zero] at hh
    exact hh rfl
  let D := (singularProductPolynomial q base).eval b
  have hD : D ≠ 0 := by
    have hDu : IsUnit ((D : ℤ) : ZMod (p^3)) := by
      change IsUnit (((singularProductPolynomial q base).eval b : ℤ) : ZMod (p^3))
      simp only [singularProductPolynomial, eval_mul, Int.cast_mul, ← heval]
      exact hu.2.1.mul hu.2.2
    intro hz
    apply hDu.ne_zero
    rw [hz, Int.cast_zero]
  have hbound (z : Coordinate) (hz : CoordinateBound J₁ J₂ z) : CoordinateBound (p : ℝ) p z :=
    ⟨hz.1.trans hJp, hz.2.trans (h₁₂.trans hJp)⟩
  have hDheight : (D.natAbs : ℝ) ≤ (p : ℝ)^24 := by
    have hprod := integer_singular_product b q base base (by simp [pencil])
    rw [Nat.cast_natAbs, Int.cast_abs]
    dsimp only [D]
    rw [← hprod, Int.cast_mul, abs_mul]
    have hbval := integer_singular_value_height (p : ℝ) (by exact_mod_cast hp.two_le)
      b hbabs q base
    convert mul_le_mul (hbval base.1 (hbound q hq) (hbound base.1 hb₁)
      (hbound base.2 hb₂) (hbound base.1 hb₁))
      (hbval base.2 (hbound q hq) (hbound base.1 hb₁)
        (hbound base.2 hb₂) (hbound base.2 hb₂)) (abs_nonneg _) (by positivity) using 1 <;> ring
  let code (e : Endpoint) :=
    ((singularValuePolynomial q base e.1).eval b, (singularValuePolynomial q base e.2).eval b)
  have hcode (x y : Coordinate) (hx : physical B.R B.V x ∈ literalBox X Y)
      (hy : physical B.R B.V y ∈ literalBox X Y)
      (hxy : (singularValuePolynomial q base x).eval b =
        (singularValuePolynomial q base y).eval b) : x = y := by
    simp only [singularValuePolynomial, eval_add, eval_neg, eval_mul] at hxy
    have hh := mul_left_cancel₀ hLn (add_left_cancel hxy)
    have hh' := congrArg (Int.castRingHom (ZMod (p^3))) hh
    simp only [coordinateLinear, PrimeCube.linear, eval_add, eval_mul, eval_C, eval_X,
      map_add, map_mul, map_intCast, hb] at hh'
    apply actual_coordinate_of_linear_residue B hr hw (RingHom.id _) hXsmall hYsmall x y hx hy
    simpa only [Int.coe_castRingHom, hb, RingHom.id_apply, mul_comm] using hh'
  have hcard : S.card ≤ (Int.divisorsAntidiag D).card := by
    apply Finset.card_le_card_of_injOn code
    · intro e he
      exact Int.mem_divisorsAntidiag.mpr ⟨integer_singular_product b q base e (hzero e he), hD⟩
    · intro e he e' he' heq
      exact Prod.ext (hcode e.1 e'.1 (hbox e he).1 (hbox e' he').1 (congrArg Prod.fst heq))
        (hcode e.2 e'.2 (hbox e he).2 (hbox e' he').2 (congrArg Prod.snd heq))
  calc
    (S.card : ℝ) ≤ ((Int.divisorsAntidiag D).card : ℝ) := by exact_mod_cast hcard
    _ ≤ C*(D.natAbs : ℝ)^(ε/24) := hdiv D hD
    _ ≤ C*((p : ℝ)^24)^(ε/24) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hDheight (by positivity)) hC.le
    _ = C*(p : ℝ)^ε := by
      rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (p : ℝ)) 24 (ε/24)]
      congr 2
      ring


/-- The original cap-and-cutoff interface is retained as a consequence of the
coordinate-height version, with the same uniform constant. -/
theorem actual_zero_polynomial_partners_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ M X Y : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)))
      (hw : IsUnit (w : ZMod (p^3))),
      2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) → J₂ ≤ J₁ → 1 ≤ J₂ →
      WordSolution (p^3) a₁ a₂ B.R B.V q base →
      IsUnit ((physical B.R B.V base.1).1 : ZMod (p^3)) →
      IsUnit ((physical B.R B.V base.2).1 : ZMod (p^3)) →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q → CoordinateBound J₁ J₂ base.1 → CoordinateBound J₁ J₂ base.2 →
      (∀ e ∈ S, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (∀ e ∈ S, pencil q base e = 0) →
      (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε := by
  obtain ⟨C, hC, hcount⟩ := actual_zero_polynomial_partners_subpower_of_coordinate_height ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp J₁ J₂ M X Y t w B a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hXsmall hYsmall h₁₂ h₂ hbase hx hy hk hq hb₁ hb₂ hbox hzero hcap hlarge
  exact hcount p hp J₁ J₂ X Y t w B a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hXsmall hYsmall h₁₂ h₂ hbase hx hy hk hq hb₁ hb₂ hbox hzero
    (original_coordinate_height p hp J₁ J₂ M h₁₂ h₂ hcap hlarge)

end
end D5.S3.Arith.CharacterSums.Original
