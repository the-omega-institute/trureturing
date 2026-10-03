/- GID: D5/S3/Quantum/Information/BFormCodeAveragedEnumerator
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/BFormCodeAveragedEnumerator
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The B-form code average of the enumerator mod p is the cosine formula (barP). -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the fibre
  count of `B ↦ Bᵀ r` onto `r^⊥` (`horth`, `hsurj`, `hperp`, `hfiberB`), the count `hcardS` of
  the B-form matrices, the character expansion `hchar` of the orthogonality constraint and the
  cosine reduction `hcos` under `t (-a) = t a`
admission_basis: open-problem-resolution (issue #11296)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.BFormCodeAveragedEnumerator

open Matrix Finset

/-- A generating matrix `(I | Bᵀ)` of a B-form code: `B` is antisymmetric with zero diagonal. -/
abbrev IsBForm {p c : ℕ} (B : Matrix (Fin c) (Fin c) (ZMod p)) : Prop :=
  Bᵀ = -B ∧ ∀ i, B i i = 0

/-- The full enumerator of the code `{(r, Bᵀ r)}` at `x_{ab} = t_a t_b`. -/
def enumerator {p c : ℕ} [NeZero p] (t : ZMod p → ℂ) (B : Matrix (Fin c) (Fin c) (ZMod p)) :
    ℂ :=
  ∑ r : Fin c → ZMod p, ∏ i, t (r i) * t ((Bᵀ *ᵥ r) i)

/-- Eq. (barP) of arXiv:2206.14825: the enumerator averaged over the `p^{c(c-1)/2}` B-form codes. -/
def claim : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (c : ℕ) (t : ZMod p → ℂ), (∀ a, t (-a) = t a) →
    (∑ B ∈ (univ : Finset (Matrix (Fin c) (Fin c) (ZMod p))).filter IsBForm, enumerator t B) /
        (p : ℂ) ^ (c * (c - 1) / 2) =
      t 0 ^ (2 * c) + ((∑ k : ZMod p, (∑ a : ZMod p, ∑ b : ZMod p,
        (Real.cos (2 * Real.pi * k.val * a.val * b.val / p) : ℂ) * t a * t b) ^ c) -
        p * t 0 ^ c * (∑ a, t a) ^ c) / (p : ℂ) ^ c

/-- Eq. (barP) holds for every prime `p`, every `c` and every even `t`. -/
theorem result : claim := by
  intro p _ c t ht
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set S : Finset (Matrix (Fin c) (Fin c) (ZMod p)) := (univ : Finset _).filter IsBForm with hS
  -- the B-form matrices are an additive subgroup
  let Sg : AddSubgroup (Matrix (Fin c) (Fin c) (ZMod p)) :=
    { carrier := {B | IsBForm B}
      add_mem' := by
        rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
        exact ⟨by rw [transpose_add, hA1, hB1, neg_add], fun i => by simp [hA2 i, hB2 i]⟩
      zero_mem' := ⟨by simp, fun _ => rfl⟩
      neg_mem' := by
        rintro A ⟨hA1, hA2⟩
        exact ⟨by rw [transpose_neg, hA1], fun i => by simp [hA2 i]⟩ }
  -- `Bᵀ r` is orthogonal to `r`
  have horth : ∀ B : Matrix (Fin c) (Fin c) (ZMod p), IsBForm B → ∀ r : Fin c → ZMod p,
      r ⬝ᵥ (Bᵀ *ᵥ r) = 0 := by
    rintro B ⟨h1, h2⟩ r
    let L : Matrix (Fin c) (Fin c) (ZMod p) := Matrix.of fun i j => if i < j then B i j else 0
    have hB : B = L - Lᵀ := by
      ext i j
      rw [Matrix.sub_apply, transpose_apply]
      simp only [L, Matrix.of_apply]
      rcases lt_trichotomy i j with h | h | h
      · rw [if_pos h, if_neg (not_lt.mpr h.le), sub_zero]
      · subst h
        rw [if_neg (lt_irrefl _), sub_zero, h2]
      · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_sub]
        have := congrFun (congrFun h1 j) i
        rwa [transpose_apply, Matrix.neg_apply] at this
    have e : r ⬝ᵥ (Lᵀ *ᵥ r) = r ⬝ᵥ (L *ᵥ r) := by
      rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
    rw [hB, transpose_sub, transpose_transpose, sub_mulVec, dotProduct_sub, e, sub_self]
  -- every vector orthogonal to `r ≠ 0` is some `Bᵀ r`
  have hsurj : ∀ r : Fin c → ZMod p, r ≠ 0 → ∀ s, r ⬝ᵥ s = 0 →
      ∃ B : Matrix (Fin c) (Fin c) (ZMod p), IsBForm B ∧ Bᵀ *ᵥ r = s := by
    intro r hr s hs
    obtain ⟨j, hj⟩ : ∃ j, r j ≠ 0 := by
      by_contra h
      push Not at h
      exact hr (funext h)
    let u : Fin c → ZMod p := Pi.single j (r j)⁻¹
    have hu : u ⬝ᵥ r = 1 := by
      simp [u, dotProduct, Pi.single_apply, hj]
    have hs' : s ⬝ᵥ r = 0 := by rw [dotProduct_comm]; exact hs
    refine ⟨vecMulVec u s - vecMulVec s u, ⟨?_, fun i => ?_⟩, ?_⟩
    · rw [transpose_sub, transpose_vecMulVec, transpose_vecMulVec, neg_sub]
    · simp [vecMulVec_apply, mul_comm]
    · ext k
      simp only [mulVec, dotProduct, transpose_apply, Matrix.sub_apply, vecMulVec_apply, sub_mul,
        Finset.sum_sub_distrib]
      have h1 : ∑ i, u i * s k * r i = s k * (u ⬝ᵥ r) := by
        rw [dotProduct, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      have h2 : ∑ i, s i * u k * r i = u k * (s ⬝ᵥ r) := by
        rw [dotProduct, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1, h2, hu, hs']
      ring
  -- the vectors orthogonal to `r ≠ 0` are a fibre of a surjective functional
  have hperp : ∀ r : Fin c → ZMod p, r ≠ 0 →
      p * ((univ : Finset (Fin c → ZMod p)).filter (fun s => r ⬝ᵥ s = 0)).card = p ^ c := by
    intro r hr
    obtain ⟨j, hj⟩ : ∃ j, r j ≠ 0 := by
      by_contra h
      push Not at h
      exact hr (funext h)
    let f : (Fin c → ZMod p) →+ ZMod p :=
      { toFun := fun s => r ⬝ᵥ s, map_zero' := dotProduct_zero r,
        map_add' := fun a b => dotProduct_add r a b }
    have hsurjf : Function.Surjective f := by
      intro a
      refine ⟨Pi.single j (a * (r j)⁻¹), ?_⟩
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dotProduct, Pi.single_apply, mul_ite,
        mul_zero, Finset.sum_ite_eq', mem_univ, if_true]
      field_simp
    have hfib : ∀ a : ZMod p, ((univ : Finset (Fin c → ZMod p)).filter fun s => f s = a).card =
        ((univ : Finset (Fin c → ZMod p)).filter fun s => f s = 0).card :=
      fun a => AddMonoidHom.card_fiber_eq_of_mem_range f (hsurjf a) (hsurjf 0)
    have htot := Finset.card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ)
      (fun _ _ => mem_univ _)
    rw [Finset.sum_congr rfl fun a _ => hfib a, sum_const, card_univ, card_univ, ZMod.card,
      smul_eq_mul, Fintype.card_fun, ZMod.card, Fintype.card_fin] at htot
    rw [htot]
    rfl
  -- the fibres of `B ↦ Bᵀ r` over the B-form matrices
  have : DecidablePred (· ∈ Sg) := fun B => (inferInstance : Decidable (IsBForm B))
  have hSg : ∀ G : Matrix (Fin c) (Fin c) (ZMod p) → ℂ, ∑ B ∈ S, G B = ∑ B : Sg, G B :=
    fun G => Finset.sum_subtype S (fun B => by simp [hS]; rfl) G
  have hcardSg : Fintype.card Sg = S.card := by
    have h1 := hSg fun _ => 1
    simp only [sum_const, nsmul_eq_mul, mul_one, card_univ] at h1
    exact_mod_cast h1.symm
  have hfiberB : ∀ r : Fin c → ZMod p, r ≠ 0 → ∀ G : (Fin c → ZMod p) → ℂ,
      (p : ℂ) ^ c * ∑ B ∈ S, G (Bᵀ *ᵥ r) =
        p * S.card * ∑ s ∈ (univ : Finset (Fin c → ZMod p)).filter (fun s => r ⬝ᵥ s = 0), G s := by
    intro r hr G
    let φ : Sg →+ (Fin c → ZMod p) :=
      { toFun := fun B => (B : Matrix (Fin c) (Fin c) (ZMod p))ᵀ *ᵥ r
        map_zero' := by simp
        map_add' := fun A B => by simp [transpose_add, add_mulVec] }
    set P := (univ : Finset (Fin c → ZMod p)).filter (fun s => r ⬝ᵥ s = 0) with hP
    have hmem : ∀ s, s ∈ Set.range φ ↔ s ∈ P := by
      intro s
      constructor
      · rintro ⟨B, rfl⟩
        simp only [hP, Finset.mem_filter, mem_univ, true_and]
        exact horth B B.2 r
      · intro hs
        simp only [hP, Finset.mem_filter, mem_univ, true_and] at hs
        obtain ⟨B, hB, hBr⟩ := hsurj r hr s hs
        exact ⟨⟨B, hB⟩, hBr⟩
    have himage : (univ : Finset Sg).image φ = P := by
      ext s
      rw [Finset.mem_image, ← hmem s]
      simp [Set.mem_range]
    set K := ((univ : Finset Sg).filter fun B => φ B = 0).card with hK
    have hfib : ∀ s ∈ P, ((univ : Finset Sg).filter fun B => φ B = s).card = K :=
      fun s hs => AddMonoidHom.card_fiber_eq_of_mem_range φ ((hmem s).2 hs)
        ((hmem 0).2 (by simp [hP]))
    have hsumK : ∑ B ∈ S, G (Bᵀ *ᵥ r) = K * ∑ s ∈ P, G s := by
      rw [hSg (fun B => G (Bᵀ *ᵥ r))]
      change ∑ B : Sg, G (φ B) = _
      rw [Finset.sum_comp, himage, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s hs => by rw [hfib s hs, nsmul_eq_mul]
    have hcardK : S.card = K * P.card := by
      rw [← hcardSg, ← card_univ, Finset.card_eq_sum_card_image φ univ, himage,
        Finset.sum_congr rfl hfib, sum_const, smul_eq_mul, mul_comm]
    have hP' : (p : ℂ) * P.card = p ^ c := by exact_mod_cast hperp r hr
    rw [hsumK, hcardK, ← hP']
    push_cast
    ring
  -- the number of B-form matrices: free entries above the diagonal
  have hcardS : S.card = p ^ (c * (c - 1) / 2) := by
    let e : {B : Matrix (Fin c) (Fin c) (ZMod p) // IsBForm B} ≃
        ({x : Fin c × Fin c // x.1 < x.2} → ZMod p) :=
      { toFun := fun B x => B.1 x.1.1 x.1.2
        invFun := fun g => ⟨Matrix.of fun i j => if h : i < j then g ⟨(i, j), h⟩
            else if h' : j < i then -g ⟨(j, i), h'⟩ else 0, by
          refine ⟨?_, fun i => by simp⟩
          ext i j
          simp only [transpose_apply, Matrix.neg_apply, Matrix.of_apply]
          rcases lt_trichotomy i j with h | h | h
          · simp [h, not_lt.mpr h.le]
          · subst h
            simp
          · simp [h, not_lt.mpr h.le]⟩
        left_inv := by
          rintro ⟨B, h1, h2⟩
          apply Subtype.ext
          ext i j
          simp only [Matrix.of_apply]
          rcases lt_trichotomy i j with h | h | h
          · simp [h]
          · subst h
            simp [h2]
          · have hij := congrFun (congrFun h1 j) i
            simp only [transpose_apply, Matrix.neg_apply] at hij
            simp [h, not_lt.mpr h.le, hij]
        right_inv := by
          intro g
          funext x
          simp [x.2] }
    have hT : Fintype.card {x : Fin c × Fin c // x.1 < x.2} = c * (c - 1) / 2 := by
      rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
      have hrow : ∀ i : Fin c, (∑ j : Fin c, if i < j then 1 else 0) = c - 1 - i := by
        intro i
        rw [← Finset.card_filter, ← Fin.card_Ioi]
        congr 1
        ext j
        simp
      rw [Finset.sum_congr rfl fun i _ => hrow i, Fin.sum_univ_eq_sum_range (fun i => c - 1 - i) c,
        Finset.sum_range_reflect (fun i => i) c, Finset.sum_range_id]
    have hSeq : S.card = Fintype.card {B : Matrix (Fin c) (Fin c) (ZMod p) // IsBForm B} := by
      rw [hS, Fintype.card_subtype]
    rw [hSeq, Fintype.card_congr e, Fintype.card_fun, ZMod.card, hT]
  -- split off `r = 0` and apply the fibre count
  have hmain : (p : ℂ) ^ c * ∑ B ∈ S, enumerator t B =
      S.card * ((p : ℂ) ^ c * t 0 ^ (2 * c) + p * ∑ r ∈ (univ : Finset (Fin c → ZMod p)).erase 0,
        ∑ s ∈ (univ : Finset (Fin c → ZMod p)).filter (fun s => r ⬝ᵥ s = 0),
          ∏ i, t (r i) * t (s i)) := by
    simp only [enumerator]
    rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (mem_univ (0 : Fin c → ZMod p)), mul_add,
      Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · simp only [mulVec_zero, Pi.zero_apply, sum_const, nsmul_eq_mul, Finset.prod_const,
        card_univ, Fintype.card_fin]
      ring
    · refine Finset.sum_congr rfl fun r hr => ?_
      rw [hfiberB r (Finset.ne_of_mem_erase hr) fun s => ∏ i, t (r i) * t (s i)]
      ring
  -- orthogonality of the standard additive character
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar with hψ
  have hind : ∀ x : ZMod p, (∑ k : ZMod p, ψ (k * x)) = if x = 0 then (p : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar p), ZMod.card]
    split_ifs <;> simp
  have hψsum : ∀ (s : Finset (Fin c)) (f : Fin c → ZMod p),
      ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  have hfac : ∀ g : Fin c → ZMod p → ℂ, ∑ x : Fin c → ZMod p, ∏ i, g i (x i) = ∏ i, ∑ a, g i a := by
    intro g
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  -- the character sum
  have hchar : (p : ℂ) * ∑ r : Fin c → ZMod p,
      ∑ s ∈ (univ : Finset (Fin c → ZMod p)).filter (fun s => r ⬝ᵥ s = 0), ∏ i, t (r i) * t (s i) =
      ∑ k : ZMod p, (∑ a : ZMod p, ∑ b : ZMod p, ψ (k * a * b) * t a * t b) ^ c := by
    calc (p : ℂ) * ∑ r : Fin c → ZMod p,
          ∑ s ∈ (univ : Finset (Fin c → ZMod p)).filter (fun s => r ⬝ᵥ s = 0),
            ∏ i, t (r i) * t (s i)
        = ∑ r : Fin c → ZMod p, ∑ s : Fin c → ZMod p,
            (∑ k : ZMod p, ψ (k * (r ⬝ᵥ s))) * ∏ i, t (r i) * t (s i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hind]
          split_ifs <;> simp
      _ = ∑ k : ZMod p, ∑ r : Fin c → ZMod p, ∑ s : Fin c → ZMod p,
            ∏ i, ψ (k * r i * s i) * t (r i) * t (s i) := by
          simp only [Finset.sum_mul]
          refine ((Finset.sum_congr rfl fun r _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ =>
            Finset.sum_congr rfl fun s _ => ?_
          rw [dotProduct, Finset.mul_sum, hψsum, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_assoc k]
          ring
      _ = ∑ k : ZMod p, (∑ a : ZMod p, ∑ b : ZMod p, ψ (k * a * b) * t a * t b) ^ c := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Fin.prod_const, ← hfac]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← hfac fun i b => ψ (k * r i * b) * t (r i) * t b]
  -- the `r = 0` row
  have hzero : ∑ s ∈ (univ : Finset (Fin c → ZMod p)).filter
      (fun s => (0 : Fin c → ZMod p) ⬝ᵥ s = 0),
      ∏ i, t ((0 : Fin c → ZMod p) i) * t (s i) = t 0 ^ c * (∑ a, t a) ^ c := by
    rw [Finset.filter_true_of_mem fun s _ => zero_dotProduct s]
    simp only [Pi.zero_apply]
    rw [hfac fun _ b => t 0 * t b, Fin.prod_const, ← Finset.mul_sum, mul_pow]
  -- cosines, from the symmetry of `t`
  have hcos : ∀ k : ZMod p, (∑ a : ZMod p, ∑ b : ZMod p, ψ (k * a * b) * t a * t b) =
      ∑ a : ZMod p, ∑ b : ZMod p,
        (Real.cos (2 * Real.pi * k.val * a.val * b.val / p) : ℂ) * t a * t b := by
    intro k
    have hflip : (∑ a : ZMod p, ∑ b : ZMod p, ψ (k * a * b) * t a * t b) =
        ∑ a : ZMod p, ∑ b : ZMod p, ψ (-(k * a * b)) * t a * t b := by
      rw [← Equiv.sum_comp (Equiv.neg (ZMod p))]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Equiv.neg_apply, ht, mul_neg, neg_mul]
    have hpt : ∀ x : ZMod p, ψ x + ψ (-x) = 2 * (Real.cos (2 * Real.pi * x.val / p) : ℂ) := by
      intro x
      rw [AddChar.map_neg_eq_inv, hψ, ZMod.stdAddChar_apply, ZMod.toCircle_apply,
        ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
      congr 1 <;> congr 1 <;> push_cast <;> ring
    have hval : ∀ a b : ZMod p, Real.cos (2 * Real.pi * (k * a * b).val / p) =
        Real.cos (2 * Real.pi * k.val * a.val * b.val / p) := by
      intro a b
      have hv : (k * a * b).val = k.val * a.val * b.val % p := by
        rw [ZMod.val_mul, ZMod.val_mul, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [hv]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hcast : ((k.val * a.val * b.val : ℕ) : ℝ) =
          ((k.val * a.val * b.val % p : ℕ) : ℝ) + p * ((k.val * a.val * b.val / p : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mod_add_div (k.val * a.val * b.val) p).symm
      push_cast at hcast
      have key : (2 * Real.pi * k.val * a.val * b.val / p : ℝ) =
          2 * Real.pi * ((k.val * a.val * b.val % p : ℕ) : ℝ) / p +
            ((k.val * a.val * b.val / p : ℕ) : ℝ) * (2 * Real.pi) := by
        rw [show (2 * Real.pi * k.val * a.val * b.val / p : ℝ) =
          2 * Real.pi * ((k.val : ℝ) * a.val * b.val) / p by ring, hcast]
        field_simp
      rw [key, Real.cos_add_nat_mul_two_pi]
    have h2 : 2 * (∑ a : ZMod p, ∑ b : ZMod p, ψ (k * a * b) * t a * t b) =
        2 * ∑ a : ZMod p, ∑ b : ZMod p,
          (Real.cos (2 * Real.pi * k.val * a.val * b.val / p) : ℂ) * t a * t b := by
      calc 2 * (∑ a : ZMod p, ∑ b : ZMod p, ψ (k * a * b) * t a * t b)
          = ∑ a : ZMod p, ∑ b : ZMod p, (ψ (k * a * b) + ψ (-(k * a * b))) * t a * t b := by
            rw [two_mul]
            nth_rewrite 2 [hflip]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hpt, hval]
            ring
    exact mul_left_cancel₀ two_ne_zero h2
  -- assembly
  have hS0 : (S.card : ℂ) ≠ 0 := by
    rw [hcardS]
    exact_mod_cast pow_ne_zero _ hp.ne_zero
  have hsplit : ∑ r ∈ (univ : Finset (Fin c → ZMod p)).erase 0,
      ∑ s ∈ (univ : Finset (Fin c → ZMod p)).filter (fun s => r ⬝ᵥ s = 0), ∏ i, t (r i) * t (s i) =
      ∑ r : Fin c → ZMod p,
        ∑ s ∈ (univ : Finset (Fin c → ZMod p)).filter (fun s => r ⬝ᵥ s = 0),
          ∏ i, t (r i) * t (s i) - t 0 ^ c * (∑ a, t a) ^ c := by
    rw [← hzero, ← Finset.add_sum_erase _ _ (mem_univ (0 : Fin c → ZMod p))]
    ring
  have hfinal : (p : ℂ) ^ c * ∑ B ∈ S, enumerator t B = S.card * ((p : ℂ) ^ c * t 0 ^ (2 * c) +
      ((∑ k : ZMod p, (∑ a : ZMod p, ∑ b : ZMod p,
        (Real.cos (2 * Real.pi * k.val * a.val * b.val / p) : ℂ) * t a * t b) ^ c) -
        p * t 0 ^ c * (∑ a, t a) ^ c)) := by
    rw [hmain, hsplit, mul_sub, hchar]
    simp only [hcos]
    ring
  have hpc : (p : ℂ) ^ c ≠ 0 := pow_ne_zero _ hp0
  have hcardSC : (p : ℂ) ^ (c * (c - 1) / 2) = S.card := by rw [hcardS]; push_cast; ring
  rw [hcardSC, div_eq_iff hS0]
  apply mul_left_cancel₀ hpc
  rw [hfinal]
  field_simp

end D5.S3.Quantum.Information.BFormCodeAveragedEnumerator
