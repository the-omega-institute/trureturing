/- GID: D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.claim; result=D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.result; claim=D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.claim
   digest: Coulter--Do Conjecture 5.4(a) fails on X(6): one coefficient is 78 versus 81. -/

/-
proof_shape: result: content (explicit noncommuting orbit vector, polynomial transport,
  support induction, unique backward path and kernel-checked coefficient computation).
  Private rising_support: content (induction on the operator word).
  Private rising_coefficient: content (the top partner forces the sole nonzero summand).
escape_witness: result itself, the coefficient inequality for the word
  J_6 J_6 J_5 J_4 J_3 e_6 at target (1 5 | 2 7 | 3 9 | 4 11 | 6 10 | 8 12).
  The support and unique-path lemmas are used to compute its coefficients.
admission_basis: open-problem-resolution (#11521; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
-/

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Data.Complex.Basic

open scoped BigOperators Polynomial
namespace D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation

/-- A partner map: its two-element orbits are precisely unordered pair partitions.
The paper's labels 1,...,2k are shifted down by one. -/
abbrev P (k : ℕ) := {p : Fin (2 * k) → Fin (2 * k) //
  Function.Involutive p ∧ ∀ x, p x ≠ x}
private instance instDecidableEqP (k) : DecidableEq (P k) :=
  inferInstanceAs (DecidableEq (Subtype _))

/-- The partner map of (1 2 | 3 4 | ...). -/
private def ep (k : ℕ) (x : Fin (2 * k)) : Fin (2 * k) :=
  ⟨if x.val % 2 = 0 then x.val + 1 else x.val - 1, by
    have := x.isLt
    split <;> omega⟩

def e (k : ℕ) : P k := ⟨ep k, by
  constructor
  · intro x
    apply Fin.ext
    simp only [ep]
    split <;> split <;> omega
  · intro x h
    have hh := congrArg Fin.val h
    simp only [ep] at hh
    split at hh <;> omega⟩

/-- Relabelling by a transposition is conjugation of the partner map. -/
def act {k} (a c : Fin (2 * k)) (p : P k) : P k :=
  ⟨fun x => Equiv.swap a c (p.val (Equiv.swap a c x)), by
    constructor
    · intro x
      simp only [Equiv.swap_apply_self]
      rw [p.property.1, Equiv.swap_apply_self]
    · intro x h
      have hh := congrArg (Equiv.swap a c) h
      simp only [Equiv.swap_apply_self] at hh
      exact p.property.2 _ hh⟩

/-- Alternate identity edges and matching edges, starting with an identity edge. -/
def walk {k} (p : P k) (x : Fin (2 * k)) : ℕ → Fin (2 * k)
  | 0 => x
  | n + 1 => if n % 2 = 0 then ep k (walk p x n) else p.val (walk p x n)

/-- The maximum label of this cycle and the parity of its first occurrence.
A component is an even cycle of at most 2k vertices. Alternating its two edge
colours visits all its vertices before repeating; a repeat has even period.
Consequently the parity of the position of its maximum is independent of
repetitions. This is the paper's charge: the maximum is positive, and every
identity or matching edge reverses charge. Here `true` denotes positive. -/
def charge {k} (p : P k) (x : Fin (2 * k)) : Bool :=
  let best := (List.range (2 * k)).foldl (fun best n =>
    let u := (walk p x n).val
    if best.1 < u then (u, n % 2 == 0) else best) (x.val, true)
  best.2

/-- Weight for the specified transposition, charges on the FIRST (output)
matching. This is the restriction of Definition 4.1 used in Definition 5.1;
the second matching is `act a c p`. The paper proves that different
witnessing transpositions give the same weight. Only this transposition-restricted
weight enters the operators. -/
def weight {K : Type*} [One K] (b : K) {k} (p : P k) (a c : Fin (2 * k)) : K :=
  if charge p a = charge p c then 1 else b

/-- Coefficient form of the paper's sum. For each transposition s, the unique
input contributing to output p is s·p, since s²=id. In particular the charges
are computed on p. `weight b p aa c` expands ω(p, (aa c)·p) using
this known transposition, so no finite search is needed. J_i is extended by
zero outside 1<=i<=k; adding that zero to the generators leaves the adjoin
unchanged. -/
def J {K : Type*} [CommRing K] (b : K) (k i : ℕ) :
    (P k → K) →ₗ[K] (P k → K) where
  toFun w p := if hi : 0 < i ∧ i ≤ k then
    ∑ a : Fin (2*i-2),
      let aa : Fin (2 * k) := ⟨a.val, by omega⟩
      let c : Fin (2 * k) := ⟨2*i-2, by omega⟩
      weight b p aa c * w (act aa c p)
    else 0
  map_add' u v := by
    funext p
    simp only [Pi.add_apply]
    split
    · simp [mul_add, Finset.sum_add_distrib]
    · simp
  map_smul' r w := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split
    · simp [Finset.mul_sum, mul_left_comm]
    · simp

def single {K : Type*} [Zero K] [One K] (k : ℕ) : P k → K :=
  fun p => if p = e k then 1 else 0

noncomputable def X {K : Type*} [CommRing K] (b : K) (k : ℕ) : Set (P k → K) :=
  {v | ∃ A ∈ Algebra.adjoin K (Set.range (J b k)), A (single k) = v}

noncomputable def claim : Prop :=
  ∀ k, 1 ≤ k → ∀ m n, 1 ≤ m → m ≤ n → n ≤ k →
    ∀ v ∈ X (RatFunc.X : RatFunc ℂ) k,
      J RatFunc.X k m (J RatFunc.X k n v) =
      J RatFunc.X k n (J RatFunc.X k m v)

/-- Increasing word J_r ... J_3 applied to the identity basis vector. -/
private def rising {K : Type*} [CommRing K] (b : K) (k : ℕ) : ℕ → P k → K
  | 0 => single k
  | n + 1 => if n + 1 ≤ 2 then single k else J b k (n + 1) (rising b k n)

/-- A word whose indices are <=r cannot change any identity pair above 2r.
This is the support invariant used to prune backward coefficient recursion. -/
private theorem rising_support {K : Type*} [CommRing K] (b : K) (k r : ℕ)
    (p : P k) (x : Fin (2 * k)) (hx : 2 * r ≤ x.val)
    (hp : p.val x ≠ ep k x) : rising b k r p = 0 := by
  induction r generalizing p with
  | zero =>
    simp only [rising, single]
    split
    · next h => exact False.elim (hp (congrArg (fun p : P k => p.val x) h))
    · rfl
  | succ r ih =>
    simp only [rising]
    split
    · simp only [single]
      split
      · next h => exact False.elim (hp (congrArg (fun p : P k => p.val x) h))
      · rfl
    · simp only [J, LinearMap.coe_mk, AddHom.coe_mk]
      split
      · next hi =>
        apply Finset.sum_eq_zero
        intro a _
        have hax : (⟨a.val, by omega⟩ : Fin (2 * k)) ≠ x := by
          intro hh; have hhval := congrArg Fin.val hh; simp only at hhval; omega
        have hcx : (⟨2*(r + 1)-2, by omega⟩ : Fin (2 * k)) ≠ x := by
          intro hh; have hhval := congrArg Fin.val hh; simp only at hhval; omega
        have hex : 2*(r + 1) ≤ (ep k x).val := by
          simp only [ep]; split <;> omega
        have haex : (ep k x) ≠ (⟨a.val, by omega⟩ : Fin (2 * k)) := by
          intro hh; have hhval := congrArg Fin.val hh; simp only at hhval; omega
        have hcex : (ep k x) ≠ (⟨2*(r + 1)-2, by omega⟩ : Fin (2 * k)) := by
          intro hh; have hhval := congrArg Fin.val hh; simp only at hhval; omega
        rw [ih (act ⟨a.val, by omega⟩ ⟨2*(r + 1)-2, by omega⟩ p) (by omega)]
        · simp
        · intro h
          have hh := congrArg (Equiv.swap (⟨a.val, by omega⟩ : Fin (2 * k))
            ⟨2*(r + 1)-2, by omega⟩) h
          simp only [act, Equiv.swap_apply_of_ne_of_ne hax.symm hcx.symm,
            Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne haex hcex] at hh
          exact hp hh
      · rfl

/-- At the top pair of an increasing word, the reverse transposition is
forced by the partner of the even endpoint. All other summands vanish by
the preceding word's support. This reduces four nested sums to one path. -/
private theorem rising_coefficient {K : Type*} [CommRing K] (b : K) (k r : ℕ)
    (hr : 3 ≤ r) (hk : r ≤ k) (p : P k) :
    rising b k r p =
      let c : Fin (2 * k) := ⟨2 * r-2, by omega⟩
      let t : Fin (2 * k) := ⟨2 * r-1, by omega⟩
      if _h : (p.val t).val < 2 * r-2 then
        weight b p (p.val t) c * rising b k (r-1) (act (p.val t) c p)
      else 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [rising, show ¬ n + 1 ≤ 2 by omega, if_false]
  let c : Fin (2 * k) := ⟨2*(n + 1)-2, by omega⟩
  let t : Fin (2 * k) := ⟨2*(n + 1)-1, by omega⟩
  change (if hi : 0 < n + 1 ∧ n + 1 ≤ k then _ else 0) = _
  rw [dif_pos (show 0 < n + 1 ∧ n + 1 ≤ k from ⟨by omega, hk⟩)]
  change (∑ a : Fin (2*(n + 1)-2), weight b p ⟨a.val, by omega⟩ c *
    rising b k n (act ⟨a.val, by omega⟩ c p)) =
    if h : (p.val t).val < 2*(n + 1)-2 then
      weight b p (p.val t) c * rising b k n (act (p.val t) c p) else 0
  have et : ep k t = c := by apply Fin.ext; simp only [ep, t, c]; split <;> omega
  have hsize : 2*(n + 1)-2 ≤ 2 * k := by omega
  have zero_term (a : Fin (2*(n + 1)-2)) (ha : a.val ≠ (p.val t).val) :
      weight b p (Fin.castLE hsize a) c *
        rising b k n (act (Fin.castLE hsize a) c p) = 0 := by
    rw [rising_support b k n _ t (by dsimp [t]; omega)]
    · simp
    · intro h
      have hat : t ≠ (Fin.castLE hsize a : Fin (2 * k)) := by
        intro hh; have := congrArg Fin.val hh; dsimp [t] at this; omega
      have hct : t ≠ c := by
        intro hh; have := congrArg Fin.val hh; dsimp [t, c] at this; omega
      have hh := congrArg (Equiv.swap (Fin.castLE hsize a : Fin (2 * k)) c) h
      simp only [act, Equiv.swap_apply_of_ne_of_ne hat hct,
        Equiv.swap_apply_self, et, Equiv.swap_apply_right] at hh
      exact ha (congrArg Fin.val hh).symm
  split
  · next h =>
    let a : Fin (2*(n + 1)-2) := ⟨(p.val t).val, h⟩
    rw [Finset.sum_eq_single a]
    · intro aa _ haa
      apply zero_term
      intro hh
      exact haa (Fin.ext hh)
    · simp
  · next h =>
    apply Finset.sum_eq_zero
    intro a _
    apply zero_term
    omega

/-- Computable, pruned coefficient recursion, with the same mathematical
transpositions and charge algorithm as J. -/
private def fastRising {K : Type*} [CommRing K] (b : K) (k : ℕ) : ℕ → P k → K
  | 0 => single k
  | n + 1 => if n + 1 ≤ 2 then single k else
    if hk : n + 1 ≤ k then fun p =>
      let c : Fin (2 * k) := ⟨2*(n + 1)-2, by omega⟩
      let t : Fin (2 * k) := ⟨2*(n + 1)-1, by omega⟩
      if h : (p.val t).val < 2*(n + 1)-2 then
        weight b p (p.val t) c * fastRising b k n (act (p.val t) c p)
      else 0
    else 0

/-- Target (1 5 | 2 7 | 3 9 | 4 11 | 6 10 | 8 12). -/
private def target : P 6 := ⟨![4,6,8,10,0,9,1,11,2,5,3,7], by
  change (∀ x, _ = x) ∧ (∀ x, _ ≠ x)
  decide⟩


/-- The polynomial model embeds into C(b) by coefficient casting and the
canonical polynomial-to-rational-function algebra map. -/
private noncomputable def embed : ℤ[X] →+* RatFunc ℂ :=
  (algebraMap ℂ[X] (RatFunc ℂ)).comp
    (Polynomial.mapRingHom (Int.castRingHom ℂ))

private def ev2 : ℤ[X] →+* ℤ := Polynomial.eval₂RingHom (RingHom.id ℤ) 2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction of the two nested finite coefficient certificates.
/-- Refutation of Coulter--Do Conjecture 5.4(a), with b an indeterminate.
All numerical certificates are local, checked by the kernel. -/
theorem result : ¬ claim := by
  classical
  have transport_J {R S : Type} [CommRing R] [CommRing S]
      (φ : R →+* S) (b : R) (k i : ℕ) (w : P k → R) :
      (fun p => φ (J b k i w p)) = J (φ b) k i (fun p => φ (w p)) := by
    funext p
    change φ (if hi : 0 < i ∧ i ≤ k then _ else 0) =
      (if hi : 0 < i ∧ i ≤ k then _ else 0)
    split
    · next hi =>
      simp only [map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simp only [weight]
      split <;> simp
    · next hi => simp only [map_zero]

  have fast_eq {K : Type} [CommRing K] (b : K) (k : ℕ) :
      ∀ r, r ≤ k → rising b k r = fastRising b k r := by
    intro r
    induction r with
    | zero => intro _; rfl
    | succ n ih =>
      intro hk
      by_cases hn : n + 1 ≤ 2
      · simp only [rising, fastRising, hn, if_true]
      · funext p
        rw [rising_coefficient b k (n + 1) (by omega) hk]
        simp only [fastRising, hn, if_false, dif_pos hk, Nat.add_sub_cancel, ih (by omega)]
  have map_rising {R S : Type} [CommRing R] [CommRing S]
      (φ : R →+* S) (b : R) (k : ℕ) :
      ∀ r, (fun p => φ (rising b k r p)) = rising (φ b) k r := by
    intro r
    induction r with
    | zero =>
      funext p
      simp only [rising, single]
      split <;> simp
    | succ n ih =>
      simp only [rising]
      split
      · funext p; simp only [single]; split <;> simp
      · rw [transport_J, ih]
  let vp : P 6 → ℤ[X] := J Polynomial.X 6 6 (rising Polynomial.X 6 6)
  let vz : P 6 → ℤ := J 2 6 6 (rising 2 6 6)
  let vc : P 6 → RatFunc ℂ := J RatFunc.X 6 6 (rising RatFunc.X 6 6)
  have hb : embed Polynomial.X = RatFunc.X := by
    simp [embed, RatFunc.algebraMap_X]
  have he : ev2 Polynomial.X = 2 := by simp [ev2]
  have hvc : (fun p => embed (vp p)) = vc := by
    dsimp only [vp, vc]
    rw [transport_J embed Polynomial.X 6 6 (rising Polynomial.X 6 6),
      map_rising embed Polynomial.X 6 6, hb]
  have hvz : (fun p => ev2 (vp p)) = vz := by
    dsimp only [vp, vz]
    rw [transport_J ev2 Polynomial.X 6 6 (rising Polynomial.X 6 6),
      map_rising ev2 Polynomial.X 6 6, he]
  have hx : vc ∈ X (RatFunc.X : RatFunc ℂ) 6 := by
    let A := J (RatFunc.X : RatFunc ℂ) 6 6 *
      J RatFunc.X 6 6 * J RatFunc.X 6 5 *
      J RatFunc.X 6 4 * J RatFunc.X 6 3
    refine ⟨A, ?_, ?_⟩
    · apply Subalgebra.mul_mem
      · apply Subalgebra.mul_mem
        · apply Subalgebra.mul_mem
          · apply Subalgebra.mul_mem
            · exact Algebra.subset_adjoin ⟨6, rfl⟩
            · exact Algebra.subset_adjoin ⟨6, rfl⟩
          · exact Algebra.subset_adjoin ⟨5, rfl⟩
        · exact Algebra.subset_adjoin ⟨4, rfl⟩
      · exact Algebra.subset_adjoin ⟨3, rfl⟩
    · rfl
  have hl : J (2 : ℤ) 6 2 (J 2 6 4 vz) target = 78 := by
    dsimp only [vz]
    rw [fast_eq (2 : ℤ) 6 6 (by omega)]
    decide +kernel
  have hr : J (2 : ℤ) 6 4 (J 2 6 2 vz) target = 81 := by
    dsimp only [vz]
    rw [fast_eq (2 : ℤ) 6 6 (by omega)]
    decide +kernel
  have hi : Function.Injective embed :=
    (RatFunc.algebraMap_injective ℂ).comp
      (Polynomial.map_injective _ (Int.cast_injective :
        Function.Injective (Int.castRingHom ℂ)))
  intro hclaim
  have h := congrFun (hclaim 6 (by omega) 2 4 (by omega) (by omega) (by omega) vc hx) target
  have hleft : embed (J Polynomial.X 6 2 (J Polynomial.X 6 4 vp) target) =
      J RatFunc.X 6 2 (J RatFunc.X 6 4 vc) target := by
    calc
      embed (J Polynomial.X 6 2 (J Polynomial.X 6 4 vp) target) =
          J (embed Polynomial.X) 6 2 (fun p => embed (J Polynomial.X 6 4 vp p)) target :=
        congrFun (transport_J embed Polynomial.X 6 2 (J Polynomial.X 6 4 vp)) target
      _ = _ := by rw [transport_J embed Polynomial.X 6 4 vp, hvc, hb]
  have hright : embed (J Polynomial.X 6 4 (J Polynomial.X 6 2 vp) target) =
      J RatFunc.X 6 4 (J RatFunc.X 6 2 vc) target := by
    calc
      embed (J Polynomial.X 6 4 (J Polynomial.X 6 2 vp) target) =
          J (embed Polynomial.X) 6 4 (fun p => embed (J Polynomial.X 6 2 vp p)) target :=
        congrFun (transport_J embed Polynomial.X 6 4 (J Polynomial.X 6 2 vp)) target
      _ = _ := by rw [transport_J embed Polynomial.X 6 2 vp, hvc, hb]
  have hp := hi (hleft.trans (h.trans hright.symm))
  have hz := congrArg ev2 hp
  have hzleft : ev2 (J Polynomial.X 6 2 (J Polynomial.X 6 4 vp) target) =
      J 2 6 2 (J 2 6 4 vz) target := by
    calc
      ev2 (J Polynomial.X 6 2 (J Polynomial.X 6 4 vp) target) =
          J (ev2 Polynomial.X) 6 2 (fun p => ev2 (J Polynomial.X 6 4 vp p)) target :=
        congrFun (transport_J ev2 Polynomial.X 6 2 (J Polynomial.X 6 4 vp)) target
      _ = _ := by rw [transport_J ev2 Polynomial.X 6 4 vp, hvz, he]
  have hzright : ev2 (J Polynomial.X 6 4 (J Polynomial.X 6 2 vp) target) =
      J 2 6 4 (J 2 6 2 vz) target := by
    calc
      ev2 (J Polynomial.X 6 4 (J Polynomial.X 6 2 vp) target) =
          J (ev2 Polynomial.X) 6 4 (fun p => ev2 (J Polynomial.X 6 2 vp p)) target :=
        congrFun (transport_J ev2 Polynomial.X 6 4 (J Polynomial.X 6 2 vp)) target
      _ = _ := by rw [transport_J ev2 Polynomial.X 6 2 vp, hvz, he]
  rw [hzleft, hzright, hl, hr] at hz
  norm_num at hz


end D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
