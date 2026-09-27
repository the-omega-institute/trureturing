/- GID: D5/S3/Quantum/SpinChains/XXChainNullspaceCount
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/XXChainNullspaceCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: For every odd prime p, OEIS A392387 (XX chain nullspace) has a(2p) = 2(6^((p-1)/2) + 1). -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the count 2 + 2·6^m is produced
  by a construction on its live proof path (local steps `hP`, the characterization of zero cosine
  sums by relations on class-state functions over ZMod p; `countA`; and `countB`, an explicit
  bijection with pairs of class states over a fundamental domain of r ↦ -1 - r)
admission_basis: open-problem-resolution (issue #10063)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.SpinChains.XXChainNullspaceCount

open Complex Polynomial Finset

/-!
OEIS A392387 (Thore Posske, 2026): `a(n)` is the dimension of the zero-energy subspace of the
periodic spin-1/2 XX Heisenberg chain on `n > 1` sites. By the Jordan–Wigner transformation the
entry states it as the number of subsets `K` of `{1,…,n}` such that the sum of cosines of the
angles `(2j + (1 + (-1)^|K|)/2)π/n`, `j ∈ K`, is zero, and conjectures
`a(2p) = 2(6^((p-1)/2) + 1)` for every odd prime `p`. Hu, Gerken and Posske (arXiv:2602.15098,
appendix on the XX model) call this count an unsolved problem.
-/

open Classical in
/-- OEIS A392387 (%C): the number of subsets `K ⊆ {1,…,n}` such that the sum of the cosines of
the angles `(2j + (1 + (-1)^|K|)/2)π/n`, `j ∈ K`, is zero. -/
noncomputable def nullspaceCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun K : Finset ℕ =>
    ∑ j ∈ K, Real.cos ((2 * (j : ℝ) + (1 + (-1 : ℝ) ^ K.card) / 2) * Real.pi / n) = 0).card

/-- OEIS A392387, Conjecture: `a(2p) = 2(6^((p-1)/2) + 1)` for every odd prime `p`. -/
def claim : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → nullspaceCount (2 * p) = 2 * (6 ^ ((p - 1) / 2) + 1)

/-- The state of a residue class `r` modulo `p`: whether its even and its odd element of
`{1,…,2p}` are taken. -/
private abbrev ClassState := ZMod 2 → Bool

/-- The subset of `{1,…,2p}` described by a class-state function: `j` is taken iff the state of
`j mod p` takes the parity `j mod 2`. -/
private def F (p : ℕ) (w : ZMod p → ClassState) : Finset ℕ :=
  (Icc 1 (2 * p)).filter fun j => w (j : ZMod p) (j : ZMod 2)

/-- The signed count `[even taken] - [odd taken]` of a class state. -/
private def zz (b : ClassState) : ℤ := (if b 0 then 1 else 0) - (if b 1 then 1 else 0)

/-- The number of taken elements of a class state. -/
private def nn (b : ClassState) : ℕ := (if b 0 then 1 else 0) + (if b 1 then 1 else 0)

/-- A fundamental domain of `r ↦ -1 - r` on `ZMod (2m+1)`: `0,…,m-1`, their images, and `m`. -/
private def emb (p m : ℕ) : Fin m ⊕ Fin m ⊕ Unit → ZMod p
  | Sum.inl i => (i.val : ZMod p)
  | Sum.inr (Sum.inl i) => -1 - (i.val : ZMod p)
  | Sum.inr (Sum.inr _) => (m : ZMod p)

/-- The state taking only the even element. -/
private def b1 : ClassState := fun ε => decide (ε = 0)

/-- The state taking only the odd element. -/
private def b2 : ClassState := fun ε => decide (ε = 1)

theorem result : claim := by
  intro p hpr hodd
  classical
  have hp : Fact p.Prime := ⟨hpr⟩
  have : NeZero p := ⟨hpr.ne_zero⟩
  obtain ⟨m, hm⟩ := id hodd
  have hpm : p = 2 * m + 1 := hm
  -- The roots of unity: `ω = exp(πi/(2p))`, `η = -ω²` a primitive `p`-th root.
  set ω : ℂ := Complex.exp (Real.pi * I / (2 * p)) with hω
  have hωc : (starRingEnd ℂ) ω = ω⁻¹ := by
    simp only [ω, ← Complex.exp_conj, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat, map_natCast, ← Complex.exp_neg]
    congr 1; ring
  have hη : IsPrimitiveRoot (-ω ^ 2) p := by
    have hcop : Nat.Coprime (m + 1) p := by
      rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
      have := hp.out.two_le
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have h := Complex.isPrimitiveRoot_exp_of_coprime (m + 1) p hp.out.ne_zero hcop
    convert h using 1
    simp only [ω, ← Complex.exp_nat_mul]
    rw [show 2 * ↑Real.pi * I * (((m + 1 : ℕ) : ℂ) / (p : ℂ)) =
      ↑Real.pi * I + ((2 : ℕ) : ℂ) * (↑Real.pi * I / (2 * p)) by
        have hk0 : (2 * (m : ℂ) + 1) ≠ 0 := by norm_cast
        rw [hpm]; push_cast; field_simp; ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have hηc : (starRingEnd ℂ) (-ω ^ 2) = (-ω ^ 2)⁻¹ := by
    rw [map_neg, map_pow, hωc]; field_simp
  set η : ℂ := -ω ^ 2 with hηdef
  have hω2 : ω ^ 2 = -η := by rw [hηdef, neg_neg]
  -- Sums over `ZMod p` as sums over `range p`.
  have sumVal : ∀ {M : Type} [AddCommMonoid M] (f : ℕ → M),
      ∑ r : ZMod p, f r.val = ∑ i ∈ range p, f i := by
    intro M _ f
    refine Finset.sum_nbij' ZMod.val (fun i => (i : ZMod p)) ?_ ?_ ?_ ?_ ?_
    · intro r _; simpa using ZMod.val_lt r
    · intro i _; simp
    · intro r _; simp
    · intro i hi; simp only [mem_range] at hi; exact ZMod.val_cast_of_lt hi
    · intro r _; rfl
  -- The only integer relations among `1, η, …, η^(p-1)` have all coefficients equal
  -- (Mathlib `IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int`), read on `ZMod p`.
  have vanishZ : ∀ c : ZMod p → ℤ, ∑ r : ZMod p, (c r : ℂ) * η ^ r.val = 0 ↔ ∀ r, c r = c 0 := by
    intro c
    have e : ∑ r : ZMod p, (c r : ℂ) * η ^ r.val =
        ∑ i : Fin p, ((c ((i : ℕ) : ZMod p) : ℤ) : ℂ) * η ^ (i : ℕ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ((c (i : ZMod p) : ℤ) : ℂ) * η ^ i) p,
        ← sumVal (fun i => ((c (i : ZMod p) : ℤ) : ℂ) * η ^ i)]
      simp
    rw [e, hη.sum_eq_zero_iff_forall_eq_int hpr (fun i : Fin p => c ((i : ℕ) : ZMod p))]
    constructor
    · intro h r
      have := h ⟨r.val, ZMod.val_lt r⟩ ⟨0, hpr.pos⟩
      simpa using this
    · intro h i j
      rw [h, h (((j : ℕ) : ZMod p))]
  have powval : ∀ a b : ZMod p, η ^ (a + b).val = η ^ a.val * η ^ b.val := by
    intro a b
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) p]
    rw [pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]
  have powneg : ∀ r : ZMod p, η ^ (-r).val = (η ^ r.val)⁻¹ := by
    intro r
    have h := powval (-r) r
    rw [neg_add_cancel, ZMod.val_zero, pow_zero] at h
    have hne : η ^ r.val ≠ 0 := pow_ne_zero _ (hη.ne_zero hp.out.ne_zero)
    field_simp
    exact h.symm
  have reZero : ∀ W : ℂ, W.re = 0 ↔ W + (starRingEnd ℂ) W = 0 := by
    intro W
    rw [Complex.add_conj]
    constructor
    · intro h; rw [h]; simp
    · intro h
      have : ((2 * W.re : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by simpa using h
      have := Complex.ofReal_injective this
      linarith
  -- Zero real part at the odd-parity angles.
  have oddChar : ∀ z : ZMod p → ℤ,
      (∑ r : ZMod p, (z r : ℂ) * η ^ r.val).re = 0 ↔ ∀ r, z r + z (-r) = z 0 + z 0 := by
    intro z
    have hconj : (starRingEnd ℂ) (∑ r : ZMod p, (z r : ℂ) * η ^ r.val) =
        ∑ r : ZMod p, (z (-r) : ℂ) * η ^ r.val := by
      rw [map_sum]
      refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun r => ?_
      simp only [map_mul, map_intCast, map_pow, hηc, Equiv.neg_apply, neg_neg, powneg, inv_pow]
    rw [reZero, hconj, ← Finset.sum_add_distrib]
    have e : ∀ r : ZMod p, (z r : ℂ) * η ^ r.val + (z (-r) : ℂ) * η ^ r.val =
        ((z r + z (-r) : ℤ) : ℂ) * η ^ r.val := fun r => by push_cast; ring
    simp only [e]
    rw [vanishZ (fun r => z r + z (-r))]
    simp
  -- Zero real part at the even-parity angles.
  have evenChar : ∀ z : ZMod p → ℤ,
      (ω * ∑ r : ZMod p, (z r : ℂ) * η ^ r.val).re = 0 ↔
        ∀ r, z (-r) - z (r - 1) = z 0 - z (-1) := by
    intro z
    have hω0 : ω ≠ 0 := by
      intro h; rw [h] at hω2; simp at hω2; exact hη.ne_zero hp.out.ne_zero hω2
    have hconj : (starRingEnd ℂ) (∑ r : ZMod p, (z r : ℂ) * η ^ r.val) =
        ∑ r : ZMod p, (z (-r) : ℂ) * η ^ r.val := by
      rw [map_sum]
      refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun r => ?_
      simp only [map_mul, map_intCast, map_pow, hηc, Equiv.neg_apply, neg_neg, powneg, inv_pow]
    have hshift : η * ∑ r : ZMod p, (z r : ℂ) * η ^ r.val =
        ∑ r : ZMod p, (z (r - 1) : ℂ) * η ^ r.val := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) _ _ fun r => ?_
      simp only [Equiv.coe_addRight, add_sub_cancel_right, powval]
      rw [show ((1 : ZMod p)).val = 1 from ZMod.val_one p]
      ring
    rw [reZero, map_mul, hωc, hconj]
    have e : ω * ∑ r : ZMod p, (z r : ℂ) * η ^ r.val +
        ω⁻¹ * ∑ r : ZMod p, (z (-r) : ℂ) * η ^ r.val =
        ω⁻¹ * ∑ r : ZMod p, ((z (-r) - z (r - 1) : ℤ) : ℂ) * η ^ r.val := by
      have : ω * ∑ r : ZMod p, (z r : ℂ) * η ^ r.val =
          ω⁻¹ * (-(η * ∑ r : ZMod p, (z r : ℂ) * η ^ r.val)) := by
        rw [neg_mul_eq_neg_mul, ← hω2]; field_simp
      rw [this, hshift, ← mul_add, neg_add_eq_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      push_cast; ring
    rw [e, mul_eq_zero, or_iff_right (inv_ne_zero hω0), vanishZ]
    simp
  have condB : ∀ z : ZMod p → ℤ,
      (∀ r, z (-r) - z (r - 1) = z 0 - z (-1)) ↔ ∀ r, z r = z (-1 - r) := by
    intro z
    have hc : (-1 : ZMod p) - (m : ZMod p) = m := by
      have h : ((2 * m : ℕ) : ZMod p) = -1 := by
        rw [show 2 * m = p - 1 by omega, Nat.cast_sub (by omega), ZMod.natCast_self]; simp
      push_cast at h
      linear_combination -h
    constructor
    · intro h
      have hD : z 0 - z (-1) = 0 := by
        have := h (-(m : ZMod p))
        rw [neg_neg, show -(m : ZMod p) - 1 = -1 - m by ring, hc] at this
        omega
      intro r
      have := h (-r)
      rw [neg_neg, show -r - 1 = -1 - r by ring] at this
      omega
    · intro h r
      have h1 := h (-r)
      have h2 := h 0
      rw [show (-1 : ZMod p) - -r = r - 1 by ring] at h1
      rw [sub_zero] at h2
      omega
  -- `j ↦ (j mod p, j mod 2)` is a bijection from `{1,…,2p}` onto `ZMod p × ZMod 2`.
  have crtInj : Set.InjOn (fun j : ℕ => ((j : ZMod p), (j : ZMod 2))) (Icc 1 (2 * p) : Finset ℕ) := by
    intro j hj j' hj' h
    simp only [coe_Icc, Set.mem_Icc] at hj hj'
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [ZMod.natCast_eq_natCast_iff] at h1 h2
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (by
      rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) even_two)
    have h3 : j ≡ j' [MOD 2 * p] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩
    rcases le_total j j' with hle | hle
    · have hd := (Nat.modEq_iff_dvd' hle).mp h3
      have : j' - j = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd := (Nat.modEq_iff_dvd' hle).mp h3.symm
      have : j - j' = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
  have crtImage : (Icc 1 (2 * p)).image (fun j : ℕ => ((j : ZMod p), (j : ZMod 2))) = univ := by
    apply Finset.eq_univ_of_card
    rw [card_image_of_injOn (crtInj), Nat.card_Icc, Fintype.card_prod, ZMod.card, ZMod.card]
    ring_nf; omega
  have sumCrt : ∀ {M : Type} [AddCommMonoid M] (g : ZMod p → ZMod 2 → M),
      ∑ j ∈ Icc 1 (2 * p), g (j : ZMod p) (j : ZMod 2) = ∑ r : ZMod p, (g r 0 + g r 1) := by
    intro M _ g
    have h := Finset.sum_image (f := fun x : ZMod p × ZMod 2 => g x.1 x.2) (crtInj)
    rw [crtImage] at h
    rw [← h, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ => Fin.sum_univ_two _
  -- Subsets of `{1,…,2p}` are exactly the sets `F p w`.
  have Finj : Function.Injective (F p) := by
    intro w w' h
    funext r ε
    have hmem : (r, ε) ∈ (Icc 1 (2 * p)).image (fun j : ℕ => ((j : ZMod p), (j : ZMod 2))) := by
      rw [crtImage]; exact mem_univ _
    obtain ⟨j, hj, hjr⟩ := mem_image.mp hmem
    simp only [Prod.mk.injEq] at hjr
    obtain ⟨rfl, rfl⟩ := hjr
    have := congrArg (fun K => j ∈ K) h
    simp only [F, mem_filter, hj, true_and, eq_iff_iff] at this
    exact Bool.eq_iff_iff.mpr this
  have Fimage : (univ : Finset (ZMod p → ClassState)).image (F p) = (Icc 1 (2 * p)).powerset := by
    apply Finset.eq_of_subset_of_card_le
    · intro K hK
      obtain ⟨w, -, rfl⟩ := mem_image.mp hK
      exact mem_powerset.mpr (filter_subset _ _)
    · rw [card_image_of_injective _ (Finj), card_powerset, Nat.card_Icc, card_univ,
        Fintype.card_fun, Fintype.card_fun, ZMod.card, ZMod.card, Fintype.card_bool]
      rw [show 2 * p + 1 - 1 = 2 * p by omega, pow_mul]
  -- Counting class-state functions.
  have zzPairCard : (univ.filter (fun ab : ClassState × ClassState => zz ab.1 = zz ab.2)).card = 6 := by
    decide
  have zzZeroCard : (univ.filter (fun b : ClassState => zz b = 0)).card = 2 := by decide
  have nnPairEven : ∀ a b : ClassState, zz a = zz b → Even (nn a + nn b) := by decide
  have nnEvenIff : ∀ b : ClassState, Even (nn b) ↔ zz b = 0 := by decide
  have valNeg : ∀ i : ℕ, i < p → ((-1 - (i : ZMod p)) : ZMod p).val = p - 1 - i := by
    intro i hi
    have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    have : ((-1 - (i : ZMod p)) : ZMod p) = ((p - 1 - i : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hp, ZMod.natCast_self]; ring
    rw [this, ZMod.val_cast_of_lt (by omega)]
  have embVal : ∀ s, (emb p m s).val = match s with
      | Sum.inl i => i.val
      | Sum.inr (Sum.inl i) => p - 1 - i.val
      | Sum.inr (Sum.inr _) => m := by
    rintro (i | i | u)
    · exact ZMod.val_cast_of_lt (by omega)
    · exact valNeg i.val (by omega)
    · exact ZMod.val_cast_of_lt (by omega)
  have embBij : Function.Bijective (emb p m) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun s t h => ?_, ?_⟩
    · have hv := congrArg ZMod.val h
      rw [embVal, embVal] at hv
      rcases s with i | i | u <;> rcases t with j | j | v <;> simp only at hv
      · exact congrArg _ (Fin.ext hv)
      · have := i.isLt; have := j.isLt; omega
      · have := i.isLt; omega
      · have := i.isLt; have := j.isLt; omega
      · exact congrArg _ (congrArg _ (Fin.ext (by have := i.isLt; have := j.isLt; omega)))
      · have := i.isLt; omega
      · have := j.isLt; omega
      · have := j.isLt; omega
      · rfl
    · simp [Fintype.card_sum, ZMod.card]; omega
  have tauEmb : ∀ s, (-1 : ZMod p) - emb p m s = emb p m (match s with
      | Sum.inl i => Sum.inr (Sum.inl i)
      | Sum.inr (Sum.inl i) => Sum.inl i
      | Sum.inr (Sum.inr u) => Sum.inr (Sum.inr u)) := by
    rintro (i | i | u)
    · simp [emb]
    · simp [emb]
    · simp only [emb]
      have h : ((2 * m : ℕ) : ZMod p) = -1 := by
        rw [show 2 * m = p - 1 by omega, Nat.cast_sub (by omega), ZMod.natCast_self]; simp
      push_cast at h
      linear_combination -h
  -- Even parity: the symmetric class-state functions with an empty-or-full middle class.
  have countB : (univ.filter (fun w : ZMod p → ClassState =>
      Even (∑ r, nn (w r)) ∧ ∀ r, zz (w r) = zz (w (-1 - r)))).card = 6 ^ m * 2 := by
    classical
    set E : Fin m ⊕ Fin m ⊕ Unit ≃ ZMod p := Equiv.ofBijective _ (embBij) with hE
    have hEs : ∀ s, E s = emb p m s := fun s => rfl
    let g : (Fin m → ClassState × ClassState) × ClassState → Fin m ⊕ Fin m ⊕ Unit → ClassState := fun xy s => match s with
      | Sum.inl i => (xy.1 i).1
      | Sum.inr (Sum.inl i) => (xy.1 i).2
      | Sum.inr (Sum.inr _) => xy.2
    let Φ : (Fin m → ClassState × ClassState) × ClassState ≃ (ZMod p → ClassState) :=
      { toFun := fun xy r => g xy (E.symm r)
        invFun := fun w => (fun i => (w (E (Sum.inl i)), w (E (Sum.inr (Sum.inl i)))),
          w (E (Sum.inr (Sum.inr ()))))
        left_inv := fun xy => by
          simp only [Equiv.symm_apply_apply, g]
        right_inv := fun w => by
          funext r
          obtain ⟨s, rfl⟩ := E.surjective r
          rcases s with i | i | u <;> simp [g] }
    have hΦ : ∀ xy s, Φ xy (E s) = g xy s := fun xy s => by
      simp [Φ]
    rw [Finset.card_filter, ← Φ.sum_comp]
    have key : ∀ xy : (Fin m → ClassState × ClassState) × ClassState,
        (Even (∑ r, nn (Φ xy r)) ∧ ∀ r, zz (Φ xy r) = zz (Φ xy (-1 - r))) ↔
          (∀ i, zz (xy.1 i).1 = zz (xy.1 i).2) ∧ zz xy.2 = 0 := by
      intro xy
      have hsum : ∑ r, nn (Φ xy r) =
          ∑ i, (nn (xy.1 i).1 + nn (xy.1 i).2) + nn xy.2 := by
        rw [← E.sum_comp]
        simp only [hΦ, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.univ_unique,
          Finset.sum_singleton, g]
        ring
      have hsym : (∀ r, zz (Φ xy r) = zz (Φ xy (-1 - r))) ↔ ∀ i, zz (xy.1 i).1 = zz (xy.1 i).2 := by
        constructor
        · intro h i
          have := h (E (Sum.inl i))
          rw [hEs, tauEmb, ← hEs, ← hEs, hΦ, hΦ] at this
          simpa [g] using this
        · intro h r
          obtain ⟨s, rfl⟩ := E.surjective r
          rw [hEs, tauEmb, ← hEs, ← hEs, hΦ, hΦ]
          rcases s with i | i | u
          · simpa [g] using h i
          · simpa [g] using (h i).symm
          · rfl
      rw [hsym, hsum]
      constructor
      · rintro ⟨hev, hs⟩
        refine ⟨hs, ?_⟩
        have h1 : Even (∑ i, (nn (xy.1 i).1 + nn (xy.1 i).2)) :=
          Finset.even_sum _ fun i _ => nnPairEven _ _ (hs i)
        exact (nnEvenIff _).mp ((Nat.even_add.mp hev).mp h1)
      · rintro ⟨hs, h0⟩
        refine ⟨?_, hs⟩
        have h1 : Even (∑ i, (nn (xy.1 i).1 + nn (xy.1 i).2)) :=
          Finset.even_sum _ fun i _ => nnPairEven _ _ (hs i)
        exact Nat.even_add.mpr (iff_of_true h1 ((nnEvenIff _).mpr h0))
    simp only [key]
    rw [Fintype.sum_prod_type]
    simp only [ite_and]
    have hA : ∀ x : Fin m → ClassState × ClassState,
        (if ∀ i, zz (x i).1 = zz (x i).2 then 1 else 0 : ℕ) =
          ∏ i, (if zz (x i).1 = zz (x i).2 then 1 else 0 : ℕ) := fun x => by
      rw [Finset.prod_boole]; simp
    have hS : (∑ y : ClassState, (if zz y = 0 then 1 else 0 : ℕ)) = 2 := by
      rw [Finset.sum_boole]; simpa using zzZeroCard
    have hR : (∑ b : ClassState × ClassState, (if zz b.1 = zz b.2 then 1 else 0 : ℕ)) = 6 := by
      rw [Finset.sum_boole]; simpa using zzPairCard
    have hinner : ∀ x : Fin m → ClassState × ClassState,
        (∑ y : ClassState, (if ∀ i, zz (x i).1 = zz (x i).2 then (if zz y = 0 then 1 else 0) else 0 : ℕ)) =
          (if ∀ i, zz (x i).1 = zz (x i).2 then 1 else 0) * 2 := fun x => by
      split_ifs <;> simp [hS]
    simp only [hinner, ← Finset.sum_mul, hA]
    rw [← Fintype.prod_sum (fun (_ : Fin m) (b : ClassState × ClassState) => (if zz b.1 = zz b.2 then 1 else 0 : ℕ))]
    simp [hR]
  -- Odd parity: only the set of even elements and the set of odd elements.
  have countA : (univ.filter (fun w : ZMod p → ClassState =>
      Odd (∑ r, nn (w r)) ∧ ∀ r, zz (w r) + zz (w (-r)) = zz (w 0) + zz (w 0))).card = 2 := by
    classical
    have hz1 : ∀ b : ClassState, zz b = 1 → b = b1 := by decide
    have hz2 : ∀ b : ClassState, zz b = -1 → b = b2 := by decide
    have hrange : ∀ b : ClassState, -1 ≤ zz b ∧ zz b ≤ 1 := by decide
    have hpar : ∀ b : ClassState, (nn b : ℤ) = zz b + 2 * (if b 1 then 1 else 0) := by decide
    have hne : (fun _ : ZMod p => b1) ≠ (fun _ => b2) := by
      intro h; have := congrFun (congrFun h 0) 0; simp [b1, b2] at this
    have hset : univ.filter (fun w : ZMod p → ClassState =>
        Odd (∑ r, nn (w r)) ∧ ∀ r, zz (w r) + zz (w (-r)) = zz (w 0) + zz (w 0)) =
          {fun _ => b1, fun _ => b2} := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hodd', hc⟩
        have h0 := hrange (w 0)
        rcases (show zz (w 0) = -1 ∨ zz (w 0) = 0 ∨ zz (w 0) = 1 by omega) with h | h | h
        · right; funext r
          have := hc r; have := hrange (w r); have := hrange (w (-r))
          exact hz2 _ (by omega)
        · exfalso
          have hs : ∑ r, zz (w r) = 0 := by
            have e1 : ∑ r, zz (w (-r)) = ∑ r, zz (w r) :=
              Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun r => by simp
            have e2 : ∑ r, (zz (w r) + zz (w (-r))) = 0 := by
              simp only [hc, h]; simp
            rw [Finset.sum_add_distrib, e1] at e2
            omega
          have hc2 : ((∑ r, nn (w r) : ℕ) : ℤ) = 2 * ∑ r, (if w r 1 then 1 else 0 : ℤ) := by
            push_cast; simp only [hpar, Finset.sum_add_distrib, hs, ← Finset.mul_sum]; ring
          have := (Int.odd_coe_nat _).mpr hodd'
          rw [hc2] at this
          exact (Int.not_even_iff_odd.mpr this) (even_two_mul _)
        · left; funext r
          have := hc r; have := hrange (w r); have := hrange (w (-r))
          exact hz1 _ (by omega)
      · rintro (rfl | rfl)
        · refine ⟨?_, fun r => rfl⟩
          have : ∑ _r : ZMod p, nn b1 = p := by simp [nn, b1, ZMod.card]
          rw [this]; exact hodd
        · refine ⟨?_, fun r => rfl⟩
          have : ∑ _r : ZMod p, nn b2 = p := by simp [nn, b2, ZMod.card]
          rw [this]; exact hodd
    rw [hset, card_pair hne]
  have powSplit : ∀ j : ℕ, (-η) ^ j = (-1 : ℂ) ^ ((j : ZMod 2)).val * η ^ ((j : ZMod p)).val := by
    intro j
    rw [neg_pow, ZMod.val_natCast, ZMod.val_natCast, ← neg_one_pow_eq_pow_mod_two]
    congr 1
    conv_lhs => rw [← Nat.mod_add_div j p]
    rw [pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]
  have cosEq : ∀ j e : ℕ, Real.cos ((2 * (j : ℝ) + e) * Real.pi / ((2 * p : ℕ) : ℝ)) =
      (ω ^ e * (ω ^ 2) ^ j).re := by
    intro j e
    rw [← pow_mul, ← pow_add, ← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast; ring
  have hm2 : (p - 1) / 2 = m := by omega
  have hZ : ∀ w : ZMod p → ClassState, ∑ j ∈ F p w, (-η) ^ j = ∑ r : ZMod p, (zz (w r) : ℂ) * η ^ r.val := by
    intro w
    rw [F, Finset.sum_filter]
    simp only [powSplit]
    rw [sumCrt (fun r ε => if w r ε then (-1 : ℂ) ^ ε.val * η ^ r.val else 0)]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h0 : ((0 : ZMod 2)).val = 0 := rfl
    have h1 : ((1 : ZMod 2)).val = 1 := rfl
    rcases hw0 : w r 0 <;> rcases hw1 : w r 1 <;> simp [zz, hw0, hw1, h0, h1]
  have hcard : ∀ w : ZMod p → ClassState, (F p w).card = ∑ r, nn (w r) := by
    intro w
    rw [F, Finset.card_filter]
    rw [sumCrt (fun r ε => if w r ε then 1 else 0)]
    rfl
  have hcos : ∀ (w : ZMod p → ClassState) (e : ℕ),
      ∑ j ∈ F p w, Real.cos ((2 * (j : ℝ) + e) * Real.pi / ((2 * p : ℕ) : ℝ)) =
        (ω ^ e * ∑ r : ZMod p, (zz (w r) : ℂ) * η ^ r.val).re := by
    intro w e
    simp only [cosEq]
    rw [← Complex.re_sum, ← Finset.mul_sum, hω2, hZ]
  have hP : ∀ w : ZMod p → ClassState,
      (∑ j ∈ F p w, Real.cos ((2 * (j : ℝ) + (1 + (-1 : ℝ) ^ (F p w).card) / 2) * Real.pi /
          ((2 * p : ℕ) : ℝ)) = 0) ↔
        ((Odd (∑ r, nn (w r)) ∧ ∀ r, zz (w r) + zz (w (-r)) = zz (w 0) + zz (w 0)) ∨
          (Even (∑ r, nn (w r)) ∧ ∀ r, zz (w r) = zz (w (-1 - r)))) := by
    intro w
    rw [hcard]
    rcases Nat.even_or_odd (∑ r, nn (w r)) with he | ho
    · have he' : (1 + (-1 : ℝ) ^ (∑ r, nn (w r))) / 2 = ((1 : ℕ) : ℝ) := by
        rw [he.neg_one_pow]; norm_num
      have hb := condB (fun r => zz (w r))
      rw [he', hcos, pow_one, evenChar, hb]
      have : ¬ Odd (∑ r, nn (w r)) := Nat.not_odd_iff_even.mpr he
      tauto
    · have ho' : (1 + (-1 : ℝ) ^ (∑ r, nn (w r))) / 2 = ((0 : ℕ) : ℝ) := by
        rw [ho.neg_one_pow]; norm_num
      rw [ho', hcos, pow_zero, one_mul, oddChar]
      have : ¬ Even (∑ r, nn (w r)) := Nat.not_even_iff_odd.mpr ho
      tauto
  have hNeZ : NeZero p := ⟨hp.out.ne_zero⟩
  rw [nullspaceCount, ← Fimage, Finset.filter_image,
    Finset.card_image_of_injective _ (Finj)]
  rw [Finset.filter_congr (fun w _ => hP w), Finset.filter_or, Finset.card_union_of_disjoint]
  · rw [countA, countB, hm2]; ring
  · rw [Finset.disjoint_filter]
    intro w _ h1 h2
    exact Nat.not_even_iff_odd.mpr h1.1 h2.1

end D5.S3.Quantum.SpinChains.XXChainNullspaceCount
