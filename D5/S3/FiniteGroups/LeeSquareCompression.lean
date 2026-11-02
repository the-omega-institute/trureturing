/- GID: D5/S3/FiniteGroups/LeeSquareCompression
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/LeeSquareCompression
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral square lifting and residue compression for arbitrary Lee covers. -/

import D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity

/-! Integer square representatives and relation-lattice compression.

The Lee-ball count, finite endomorphism argument, and determinant/index laws are
classical. No literature novelty or current-publication priority is claimed.

proof_shape: square_hole_forces_radius_divisibility: content.
escape_witness: the two neighboring parity-fiber representatives force opposite
extreme first coordinates and a lattice displacement of 2(s+1).
proof_shape: kernel_coordinates_dvd: bind-only; consumer: arbitrary_pair_upper_bound.
proof_shape: large_index_square_lift: content.
escape_witness: the hole-induced scaled cover has radius q-1 and contradicts
the actual quotient-index threshold, with the radius-two exception excluded.
proof_shape: lattice_upper_bound: content.
consumer: arbitrary_pair_upper_bound and BajnokBeattyFiniteUpper.finite_noncyclic_upper_dichotomy.
proof_shape: arbitrary_pair_upper_bound: content.
escape_witness: residue_rectangle yields the shortest progression bound for the
actual relation lattice of every covering pair; integer parity sharpens the order.
admission_basis: escape-witness.
The private counting and index adapters are consumed on these proof paths.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.LeeSquareCompression

open NearSquareLatticeRigidity BajnokBeattyCayleyNecessity

/-- Every coset has a representative in the centered integer square. -/
def SquareCovers (L : Submodule ℤ Plane) (s : ℤ) : Prop :=
  ∀ z : Plane, ∃ r : Plane, (|r 0| ≤ s ∧ |r 1| ≤ s) ∧ z - r ∈ L

theorem lee_iff_square (x y s : ℤ) :
    |x| + |y| ≤ s ↔ |x+y| ≤ s ∧ |x-y| ≤ s := by
  simp only [abs_le]
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  all_goals simp only [abs_of_nonneg, abs_of_nonpos, hx, hy]
  all_goals omega

private theorem parity_preimage (z : Plane) (hz : 2 ∣ z 0 + z 1) :
    ∃ w : Plane, sumDiff w = z := by
  obtain ⟨a, ha⟩ := hz
  refine ⟨![a, z 0-a], ?_⟩
  ext i
  fin_cases i <;> simp [sumDiff] <;> omega

private theorem covered_range (K : Submodule ℤ Plane) {s : ℤ}
    (hcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ s ∧ z-r ∈ K)
    {z : Plane} (hz : 2 ∣ z 0+z 1) :
    ∃ r : Plane, (|r 0| ≤ s ∧ |r 1| ≤ s) ∧ z-r ∈ K.map sumDiff := by
  obtain ⟨w, hw⟩ := parity_preimage z hz
  obtain ⟨r, hr, hm⟩ := hcover w
  refine ⟨sumDiff r, (lee_iff_square _ _ _).mp hr, ?_⟩
  exact ⟨w-r, hm, by rw [map_sub, hw]⟩

/-- A hole in the lifted square forces the radius plus one to be divisible by
any odd common coordinate divisor of the original relation lattice. -/
theorem square_hole_forces_radius_divisibility
    (K : Submodule ℤ Plane) {c s : ℤ} (hc : Odd c)
    (hdiv : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1)
    (hcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ s ∧ z-r ∈ K)
    (hhole : ¬ SquareCovers (K.map sumDiff) s) : c ∣ s+1 := by
  classical
  obtain ⟨z, hz⟩ := not_forall.mp hhole
  have hzpar : ¬ 2 ∣ z 0+z 1 := by
    intro hp
    exact hz (covered_range K hcover hp)
  have hpminus : 2 ∣ (z-(![1,0] : Plane)) 0 + (z-(![1,0] : Plane)) 1 := by
    simp only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      sub_zero]
    omega
  have hpplus : 2 ∣ (z+(![1,0] : Plane)) 0 + (z+(![1,0] : Plane)) 1 := by
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      add_zero]
    omega
  obtain ⟨a, ha, hma⟩ := covered_range K hcover hpminus
  obtain ⟨b, hb, hmb⟩ := covered_range K hcover hpplus
  have hax : a 0 = s := by
    by_contra hn
    apply hz
    refine ⟨a+![1,0], ?_, ?_⟩
    · simpa only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        add_zero] using
        (show |a 0+1| ≤ s ∧ |a 1| ≤ s from ⟨by
          have := abs_le.mp ha.1
          apply abs_le.mpr
          omega, ha.2⟩)
    · convert hma using 1; abel
  have hbx : b 0 = -s := by
    by_contra hn
    apply hz
    refine ⟨b-![1,0], ?_, ?_⟩
    · simpa only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        sub_zero] using
        (show |b 0-1| ≤ s ∧ |b 1| ≤ s from ⟨by
          have := abs_le.mp hb.1
          apply abs_le.mpr
          omega, hb.2⟩)
    · convert hmb using 1; abel
  obtain ⟨u, hu, heu⟩ := hma
  obtain ⟨v, hv, hev⟩ := hmb
  have hdu : c ∣ (sumDiff u) 0 := (hdiv u hu).1.add (hdiv u hu).2
  have hdv : c ∣ (sumDiff v) 0 := (hdiv v hv).1.add (hdiv v hv).2
  have hcoordu := congrFun heu 0
  have hcoordv := congrFun hev 0
  have htwice : c ∣ 2*(s+1) := by
    convert hdv.sub hdu using 1
    simp only [Pi.sub_apply, Pi.add_apply, Matrix.cons_val_zero] at hcoordu hcoordv
    omega
  obtain ⟨d, hd⟩ := hc
  obtain ⟨e, he⟩ := htwice
  refine ⟨(s+1)-d*e, ?_⟩
  linear_combination -(s+1)*hd - d*he

/-- The invariant-factor target; both cyclic factors are multiples of `c`. -/
abbrev Target (c k : ℕ) := ZMod c × ZMod (c*k)

private def reduceTarget (c k : ℕ) : Target c k →+ (Fin 2 → ZMod c) where
  toFun g := ![g.1, ZMod.castHom (dvd_mul_right c k) (ZMod c) g.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' g h := by ext i; fin_cases i <;> simp

private theorem reduceTarget_surjective (c k : ℕ) :
    Function.Surjective (reduceTarget c k) := by
  intro z
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective (dvd_mul_right c k) (z 1)
  refine ⟨(z 0, a), ?_⟩
  ext i
  fin_cases i
  · rfl
  · exact ha

/-- For every surjective coefficient map, relations are coordinatewise divisible
by the first invariant factor. No generator normal form is imposed. -/
theorem kernel_coordinates_dvd {c k : ℕ} (hc : 0 < c)
    (f : Plane →+ Target c k) (hf : Function.Surjective f)
    {z : Plane} (hz : f z = 0) : (c : ℤ) ∣ z 0 ∧ (c : ℤ) ∣ z 1 := by
  letI : NeZero c := ⟨by omega⟩
  let g := (reduceTarget c k).comp f
  let B := Pi.basisFun (ZMod c) (Fin 2)
  let A : (Fin 2 → ZMod c) →ₗ[ZMod c] (Fin 2 → ZMod c) :=
    B.constr (ZMod c) ![g ![1, 0], g ![0, 1]]
  have hA : ∀ w : Plane, A (fun i => (w i : ZMod c)) = g w := by
    intro w
    calc
      _ = (w 0 : ZMod c) • g ![1, 0] + (w 1 : ZMod c) • g ![0, 1] := by
        simp [A, B, Module.Basis.constr_apply_fintype, Fin.sum_univ_two]
      _ = w 0 • g ![1, 0] + w 1 • g ![0, 1] := by
        simp only [Int.cast_smul_eq_zsmul]
      _ = g (w 0 • ![1, 0] + w 1 • ![0, 1]) := by
        rw [map_add, map_zsmul, map_zsmul]
      _ = g w := by
        congr 1
        ext i
        fin_cases i <;> simp
  have hsurj : Function.Surjective A := by
    intro v
    obtain ⟨w, hw⟩ := (reduceTarget_surjective c k).comp hf v
    exact ⟨fun i => (w i : ZMod c), (hA w).trans hw⟩
  have hinj : Function.Injective A := Finite.injective_iff_surjective.mpr hsurj
  have he : (fun i => (z i : ZMod c)) = 0 := by
    apply hinj
    rw [hA]
    simp [g, hz]
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun he 0),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun he 1)⟩

private theorem kernel_index {c k : ℕ} (f : Plane →+ Target c k)
    (hf : Function.Surjective f) : f.ker.index = c^2*k := by
  rw [AddSubgroup.index_ker, f.range_eq_top_of_surjective hf, AddSubgroup.card_top]
  simp [Target, Nat.card_prod, Nat.card_zmod]
  ring

abbrev LeeCode (r : ℕ) :=
  (Fin (r+1) × Fin (r+1)) ⊕ (Fin r × Fin r)

def decodeLee (r : ℕ) : LeeCode r → Plane
  | .inl (a,b) => ![(a : ℤ)+(b : ℤ)-r, (a : ℤ)-(b : ℤ)]
  | .inr (a,b) => ![(a : ℤ)+(b : ℤ)+1-r, (a : ℤ)-(b : ℤ)]

theorem leeCode_complete {r : ℕ} {z : Plane}
    (hz : |z 0| + |z 1| ≤ (r : ℤ)) : ∃ a : LeeCode r, decodeLee r a = z := by
  have hs := (lee_iff_square _ _ _).mp hz
  have h0 := abs_le.mp hs.1
  have h1 := abs_le.mp hs.2
  let u := z 0+z 1+r
  let v := z 0-z 1+r
  have hu : 0 ≤ u ∧ u ≤ 2*r := by dsimp [u]; omega
  have hv : 0 ≤ v ∧ v ≤ 2*r := by dsimp [v]; omega
  by_cases hp : u % 2 = 0
  · have hvp : v % 2 = 0 := by dsimp [u,v] at *; omega
    let a : Fin (r+1) := ⟨(u/2).toNat, by omega⟩
    let b : Fin (r+1) := ⟨(v/2).toNat, by omega⟩
    refine ⟨.inl (a,b), ?_⟩
    ext i
    fin_cases i <;> simp [decodeLee, a, b] <;> dsimp [u,v] at * <;> omega
  · have hvp : v % 2 = 1 := by dsimp [u,v] at *; omega
    let a : Fin r := ⟨(u/2).toNat, by omega⟩
    let b : Fin r := ⟨(v/2).toNat, by omega⟩
    refine ⟨.inr (a,b), ?_⟩
    ext i
    fin_cases i <;> simp [decodeLee, a, b] <;> dsimp [u,v] at * <;> omega

def dilation (c : ℤ) : Plane →ₗ[ℤ] Plane := c • LinearMap.id

private theorem scaled_cover (K : Submodule ℤ Plane) {c q : ℤ} (hc : 0 < c)
    (hdiv : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1)
    (hcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ c*q-1 ∧ z-r ∈ K) :
    ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ q-1 ∧
      z-r ∈ K.comap (dilation c) := by
  intro z
  obtain ⟨w, hw, hm⟩ := hcover (c • z)
  obtain ⟨hx, hy⟩ := hdiv _ hm
  have hcx : c ∣ w 0 := by
    have ht : c ∣ (c • z) 0 := by exact dvd_mul_right c (z 0)
    have : c ∣ (c • z) 0 - w 0 := hx
    simpa using ht.sub this
  have hcy : c ∣ w 1 := by
    have ht : c ∣ (c • z) 1 := by exact dvd_mul_right c (z 1)
    have : c ∣ (c • z) 1 - w 1 := hy
    simpa using ht.sub this
  obtain ⟨x,hx⟩ := hcx
  obtain ⟨y,hy⟩ := hcy
  have he : w = c • (![x,y] : Plane) := by
    ext i
    fin_cases i <;> simp [hx,hy]
  refine ⟨![x,y], ?_, ?_⟩
  · change |x| + |y| ≤ q-1
    have hw' : c*(|x| + |y|) ≤ c*q-1 := by
      simpa [he, abs_mul, abs_of_pos hc, mul_add] using hw
    nlinarith
  · change c • (z-![x,y]) ∈ K
    rw [smul_sub, ← he]
    exact hm

private theorem lee_index_bound (K : Submodule ℤ Plane) {r : ℕ}
    (hcover : ∀ z : Plane, ∃ w : Plane, |w 0| + |w 1| ≤ (r : ℤ) ∧ z-w ∈ K) :
    K.toAddSubgroup.index ≤ (r+1)^2+r^2 := by
  let f : LeeCode r → Plane ⧸ K := fun a => Submodule.Quotient.mk (decodeLee r a)
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective K g
    obtain ⟨w,hw,hm⟩ := hcover z
    obtain ⟨a,ha⟩ := leeCode_complete hw
    refine ⟨a, ?_⟩
    change Submodule.Quotient.mk (decodeLee r a) = Submodule.Quotient.mk z
    rw [ha]
    exact (Submodule.Quotient.eq K).mpr (by simpa only [neg_sub] using K.neg_mem hm)
  change Nat.card (Plane ⧸ K) ≤ _
  have hi := Nat.card_le_card_of_surjective f hf
  simpa [f, LeeCode, Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_prod, pow_two] using hi

private theorem dilation_injective {c : ℤ} (hc : c ≠ 0) :
    Function.Injective (dilation c) := by
  intro x y h
  ext i
  have hi := congrFun h i
  change c*x i = c*y i at hi
  exact mul_left_cancel₀ hc hi

private theorem dilation_index (c : ℤ) (hc : c ≠ 0) :
    (dilation c).range.toAddSubgroup.index = c.natAbs^2 := by
  have h := Submodule.natAbs_det_equiv (dilation c).range
    (LinearEquiv.ofInjective (dilation c) (dilation_injective hc))
  change (LinearMap.det (dilation c)).natAbs =
    Nat.card (Plane ⧸ (dilation c).range) at h
  change Nat.card (Plane ⧸ (dilation c).range) = _
  simpa only [dilation, LinearMap.det_smul, LinearMap.det_id, Module.finrank_pi,
    Fintype.card_fin, mul_one, Int.natAbs_pow] using h.symm

theorem scaled_index (K : Submodule ℤ Plane) {c : ℤ} (hc : c ≠ 0)
    (hdiv : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1) :
    K.toAddSubgroup.index =
      (K.comap (dilation c)).toAddSubgroup.index*c.natAbs^2 := by
  have hm : (K.comap (dilation c)).map (dilation c) = K := by
    apply le_antisymm
    · rintro z ⟨w,hw,rfl⟩
      exact hw
    · intro z hz
      obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := hdiv z hz
      have he : dilation c ![x,y] = z := by
        ext i
        fin_cases i <;> simp [dilation] <;> omega
      exact ⟨![x,y], by change dilation c ![x,y] ∈ K; rw [he]; exact hz, he⟩
  have hi := AddSubgroup.index_map_of_injective
    (H := (K.comap (dilation c)).toAddSubgroup)
    (f := (dilation c).toAddMonoidHom) (dilation_injective hc)
  change ((K.comap (dilation c)).map (dilation c)).toAddSubgroup.index =
    (K.comap (dilation c)).toAddSubgroup.index*
      (dilation c).range.toAddSubgroup.index at hi
  rwa [hm, dilation_index c hc] at hi

/-- Above the quadratic order threshold, every odd-divisible Lee relation lattice
lifts to a cover by the full integer square. The radius-two boundary is excluded. -/
theorem large_index_square_lift (K : Submodule ℤ Plane) {c s : ℤ}
    (hc : 3 ≤ c) (hcodd : Odd c) (hs : 3 ≤ s)
    (hdiv : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1)
    (hcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ s ∧ z-r ∈ K)
    (hindex : 2*s^2 < (K.toAddSubgroup.index : ℤ)) :
    SquareCovers (K.map sumDiff) s := by
  by_contra hh
  obtain ⟨q,hq⟩ := square_hole_forces_radius_divisibility K hcodd hdiv hcover hh
  have hqpos : 1 ≤ q := by nlinarith
  let L := K.comap (dilation c)
  have hcovL : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ q-1 ∧ z-r ∈ L := by
    apply scaled_cover K (by omega) hdiv
    intro z
    obtain ⟨r,hr,hm⟩ := hcover z
    exact ⟨r, by omega, hm⟩
  let r := (q-1).toNat
  have hr : (r : ℤ) = q-1 := by dsimp [r]; omega
  have hbound := lee_index_bound L (r := r) (by simpa [hr] using hcovL)
  have hboundZ : (L.toAddSubgroup.index : ℤ) ≤ 2*q^2-2*q+1 := by
    have hh := Int.ofNat_le.mpr hbound
    push_cast at hh
    rw [hr] at hh
    nlinarith
  have hi := scaled_index K (c := c) (by omega) hdiv
  have hiZ : (K.toAddSubgroup.index : ℤ) = (L.toAddSubgroup.index : ℤ)*c^2 := by
    have hh := congrArg (fun n : ℕ => (n : ℤ)) hi
    simpa [L, Int.natCast_natAbs, abs_of_pos (show 0 < c by omega)] using hh
  have hupper : (K.toAddSubgroup.index : ℤ) ≤ c^2*(2*q^2-2*q+1) := by
    nlinarith [mul_le_mul_of_nonneg_right hboundZ (sq_nonneg c)]
  have hstrict : c^2*(2*q^2-2*q+1) < 2*s^2 := by
    have hs' : s = c*q-1 := by omega
    rw [hs']
    by_cases hc3 : c = 3
    · subst c
      have hq2 : 2 ≤ q := by omega
      nlinarith
    · have hc4 : 4 ≤ c := by omega
      have hnonneg : 0 ≤ (q-1)*(2*c*(c-2)) :=
        mul_nonneg (by omega) (mul_nonneg (by omega) (by omega))
      have hsmall : 0 ≤ (c-4)*c := mul_nonneg (by omega) (by omega)
      nlinarith
  omega

private theorem rectangle_index_bound (L : Submodule ℤ Plane) {m : ℤ}
    (hcover : RectangleCovers L m m) : (L.toAddSubgroup.index : ℤ) ≤ m^2 := by
  classical
  have hm : 0 < m := by
    obtain ⟨x,y,hx,hxm,hy,hym,_⟩ := hcover 0
    omega
  let f : Fin m.toNat × Fin m.toNat → Plane ⧸ L :=
    fun a => Submodule.Quotient.mk ![(a.1 : ℤ),(a.2 : ℤ)]
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective L g
    obtain ⟨x,y,hx,hxm,hy,hym,hmem⟩ := hcover z
    refine ⟨(⟨x.toNat, by omega⟩,⟨y.toNat, by omega⟩), ?_⟩
    change Submodule.Quotient.mk ![(x.toNat : ℤ),(y.toNat : ℤ)] = Submodule.Quotient.mk z
    simp only [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]
    exact (Submodule.Quotient.eq L).mpr (by simpa only [neg_sub] using L.neg_mem hmem)
  have hi := Nat.card_le_card_of_surjective f hf
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin] at hi
  change Nat.card (Plane ⧸ L) ≤ _ at hi
  have hiZ := Int.ofNat_le.mpr hi
  push_cast at hiZ
  rw [Int.toNat_of_nonneg (by omega)] at hiZ
  change (Nat.card (Plane ⧸ L) : ℤ) ≤ _
  nlinarith

theorem residue_rectangle (M : Submodule ℤ Plane) {c s : ℤ} (hc : 0 < c)
    (hdiv : ∀ z ∈ M, c ∣ z 0 ∧ c ∣ z 1)
    (hcover : ∀ z : Plane, ∃ r : Plane, (|r 0| ≤ s ∧ |r 1| ≤ s) ∧
      (![(-s+(2*s+1)%c),(-s+(2*s+1)%c)] + c • z)-r ∈ M) :
    RectangleCovers (M.comap (dilation c)) ((2*s+1)/c) ((2*s+1)/c) := by
  intro z
  obtain ⟨r,hr,hm⟩ := hcover z
  let a := -s+(2*s+1)%c
  have hrem0 : 0 ≤ (2*s+1)%c := Int.emod_nonneg _ (by omega)
  have hremc : (2*s+1)%c < c := Int.emod_lt_of_pos _ hc
  have he := Int.mul_ediv_add_emod (2*s+1) c
  obtain ⟨hd0,hd1⟩ := hdiv _ hm
  have hcoord (i : Fin 2) (hd : c ∣ (![a,a]+c • z-r) i) : c ∣ r i-a := by
    have ht : c ∣ c*z i := dvd_mul_right c (z i)
    have hv : (![a,a] : Plane) i = a := by fin_cases i <;> rfl
    change c ∣ (![a,a] : Plane) i+c*z i-r i at hd
    rw [hv] at hd
    convert ht.sub hd using 1; ring
  obtain ⟨x,hx⟩ := hcoord 0 hd0
  obtain ⟨y,hy⟩ := hcoord 1 hd1
  have hb0 := abs_le.mp hr.1
  have hb1 := abs_le.mp hr.2
  have hx0 : 0 ≤ x := by dsimp [a] at hx; nlinarith
  have hy0 : 0 ≤ y := by dsimp [a] at hy; nlinarith
  have hxm : x < (2*s+1)/c := by dsimp [a] at hx; nlinarith
  have hym : y < (2*s+1)/c := by dsimp [a] at hy; nlinarith
  refine ⟨x,y,hx0,hxm,hy0,hym,?_⟩
  change c • (z-![x,y]) ∈ M
  convert hm using 1
  ext i
  fin_cases i
  · change c*(z 0-x) = (-s+(2*s+1)%c)+c*z 0-r 0
    dsimp [a] at hx
    nlinarith
  · change c*(z 1-y) = (-s+(2*s+1)%c)+c*z 1-r 1
    dsimp [a] at hy
    nlinarith

theorem mapped_index (K : Submodule ℤ Plane) :
    (K.map sumDiff).toAddSubgroup.index = K.toAddSubgroup.index*2 := by
  have hi := AddSubgroup.index_map_of_injective
    (H := K.toAddSubgroup) (f := sumDiff.toAddMonoidHom) sumDiff_injective
  change (K.map sumDiff).toAddSubgroup.index =
    K.toAddSubgroup.index*sumDiff.range.toAddSubgroup.index at hi
  rwa [sumDiff_index] at hi

private theorem lattice_compression_bound (K : Submodule ℤ Plane) {c s : ℤ}
    (hc : 2 ≤ c) (hs : 3 ≤ s)
    (hdiv : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1)
    (hcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ s ∧ z-r ∈ K)
    (hindex : 2*s^2 < (K.toAddSubgroup.index : ℤ)) :
    2*(K.toAddSubgroup.index : ℤ) ≤ (c*((2*s+1)/c))^2 := by
  let M := K.map sumDiff
  have hMdiv : ∀ z ∈ M, c ∣ z 0 ∧ c ∣ z 1 := by
    rintro z ⟨w,hw,rfl⟩
    exact ⟨(hdiv w hw).1.add (hdiv w hw).2,
      (hdiv w hw).1.sub (hdiv w hw).2⟩
  have hrect : RectangleCovers (M.comap (dilation c)) ((2*s+1)/c) ((2*s+1)/c) := by
    apply residue_rectangle M (by omega) hMdiv
    rcases Int.even_or_odd c with heven | hodd
    · intro z
      apply covered_range K hcover
      obtain ⟨d,hd⟩ := heven
      refine ⟨(-s+(2*s+1)%c)+d*(z 0+z 1), ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [hd]
      ring
    · have hc3 : 3 ≤ c := by obtain ⟨d,hd⟩ := hodd; omega
      intro z
      exact large_index_square_lift K hc3 hodd hs hdiv hcover hindex _
  have hb := rectangle_index_bound _ hrect
  have hi := scaled_index M (c := c) (by omega) hMdiv
  have hiZ := congrArg (fun n : ℕ => (n : ℤ)) hi
  have hmap := congrArg (fun n : ℕ => (n : ℤ)) (mapped_index K)
  push_cast at hiZ hmap
  rw [abs_of_pos (show 0 < c by omega)] at hiZ
  have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg c)
  change (M.toAddSubgroup.index : ℤ) = _ at hmap
  nlinarith

/-- Uniform lattice-index upper bound, without choosing a product normal form.
The actual kernel index is used throughout; `scaled_index` supplies the integral
multiple of the square of the common coordinate divisor needed for parity. -/
theorem lattice_upper_bound (K : Submodule ℤ Plane) {c s : ℤ}
    (hc : 2 ≤ c) (hs : 3 ≤ s)
    (hdiv : ∀ z ∈ K, c ∣ z 0 ∧ c ∣ z 1)
    (hcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ s ∧ z-r ∈ K) :
    (K.toAddSubgroup.index : ℤ) ≤ 2*s^2 ∨
      (Odd c ∧ c ∣ 2*s+1 ∧
        2*(K.toAddSubgroup.index : ℤ) ≤ (2*s+1)^2-c^2) := by
  by_cases hlow : (K.toAddSubgroup.index : ℤ) ≤ 2*s^2
  · exact Or.inl hlow
  right
  have hcomp := lattice_compression_bound K hc hs hdiv hcover (by omega)
  let m := (2*s+1)/c
  let r := (2*s+1)%c
  have hm : 0 ≤ m := Int.ediv_nonneg (by omega) (by omega)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrc : r < c := Int.emod_lt_of_pos _ (by omega)
  have hn : c*m+r = 2*s+1 := Int.mul_ediv_add_emod _ _
  have hr : r = 0 := by
    by_contra hne
    have hr1 : 1 ≤ r := by omega
    have ht : 0 ≤ c*m := mul_nonneg (by omega) hm
    have hu : c*m ≤ 2*s := by omega
    have hprod := mul_nonneg (show 0 ≤ 2*s-c*m by omega)
      (show 0 ≤ 2*s+c*m by positivity)
    change 2*(K.toAddSubgroup.index : ℤ) ≤ (c*m)^2 at hcomp
    nlinarith
  have hn' : c*m = 2*s+1 := by omega
  have hoddprod : Odd (c*m) := by rw [hn']; exact ⟨s, by ring⟩
  have hcodd := (Int.odd_mul.mp hoddprod).1
  have hmodd := (Int.odd_mul.mp hoddprod).2
  refine ⟨hcodd, ⟨m, hn'.symm⟩, ?_⟩
  let k := (K.comap (dilation c)).toAddSubgroup.index
  have hi : (K.toAddSubgroup.index : ℤ) = (k : ℤ)*c^2 := by
    have hh := congrArg (fun n : ℕ => (n : ℤ))
      (scaled_index K (c := c) (by omega) hdiv)
    simpa [k, Int.natCast_natAbs, abs_of_pos (show 0 < c by omega)] using hh
  have hkbound : 2*(k : ℤ) ≤ m^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (show 0 < c by omega))).mp
    change 2*(K.toAddSubgroup.index : ℤ) ≤ (c*m)^2 at hcomp
    nlinarith only [hcomp, hi]
  have hround : 2*(k : ℤ) ≤ m^2-1 := by
    obtain ⟨d,hd⟩ := hmodd
    have heven : Even (m^2-1) := by
      refine ⟨2*d*(d+1),?_⟩
      rw [hd]
      ring
    obtain ⟨e,he⟩ := heven
    omega
  have hbound := mul_le_mul_of_nonneg_left hround (sq_nonneg c)
  have hsq := congrArg (fun x : ℤ => x^2) hn'
  nlinarith only [hbound, hsq, hi]

/-- Uniform upper bound for every signed covering pair in the invariant-factor
target, including the exceptional odd-divisor constraint above the baseline. -/
theorem arbitrary_pair_upper_bound {c k : ℕ} {s : ℤ}
    (hc : 2 ≤ c) (_hk : 1 ≤ k) (hs : 3 ≤ s) (a b : Target c k)
    (hcover : ∀ g : Target c k, ∃ x y : ℤ,
      |x| + |y| ≤ s ∧ x • a+y • b = g) :
    (c : ℤ)^2*k ≤ 2*s^2 ∨
      (Odd (c : ℤ) ∧ (c : ℤ) ∣ 2*s+1 ∧
        2*((c : ℤ)^2*k) ≤ (2*s+1)^2-(c : ℤ)^2) := by
  let f : Plane →+ Target c k := {
    toFun := fun z => z 0 • a+z 1 • b
    map_zero' := by simp
    map_add' := by
      intro z w
      change (z 0+w 0) • a+(z 1+w 1) • b =
        (z 0 • a+z 1 • b)+(w 0 • a+w 1 • b)
      rw [add_zsmul, add_zsmul]
      abel }
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨x,y,_,he⟩ := hcover g
    exact ⟨![x,y],he⟩
  let K := f.toIntLinearMap.ker
  have hKdiv : ∀ z ∈ K, (c : ℤ) ∣ z 0 ∧ (c : ℤ) ∣ z 1 := by
    intro z hz
    exact kernel_coordinates_dvd (by omega) f hf hz
  have hKcover : ∀ z : Plane, ∃ r : Plane, |r 0| + |r 1| ≤ s ∧ z-r ∈ K := by
    intro z
    obtain ⟨x,y,hxy,he⟩ := hcover (f z)
    refine ⟨![x,y],hxy,?_⟩
    change f (z-![x,y]) = 0
    rw [map_sub]
    change f z-(x • a+y • b) = 0
    rw [he, sub_self]
  have hi : (K.toAddSubgroup.index : ℤ) = (c : ℤ)^2*k := by
    exact_mod_cast kernel_index f hf
  simpa only [hi] using
    (lattice_upper_bound K (c := (c : ℤ)) (by exact_mod_cast hc) hs hKdiv hKcover)

end D5.S3.FiniteGroups.LeeSquareCompression
