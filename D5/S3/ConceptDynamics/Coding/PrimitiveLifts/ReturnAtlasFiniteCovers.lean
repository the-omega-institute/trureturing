/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers
   generality: G
   mirror - B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers
   mirror - E: none(waiver:symbolic - structural - theorems)
   anchors: []
   utility: none
   digest: Return atlas maps have explicit signed finite fibers and a holonomy - power criterion. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.TwoOrbitSquareRootCriterion

/-! Finite covers of complete signed return atlases over arbitrary groups. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ReturnAtlasFiniteCovers

open PrimitiveLiftRootCriterion TwoOrbitSquareRootCriterion
universe u v w
variable {H : Type u} [Group H] {X : Type v} {Y : Type w}
  (A : ReturnAtlas H X) (B : ReturnAtlas H Y)

private theorem anchored (f : X → Y)
    (hf : ∀ a x, f (A.deck a x) = B.deck a (f x))
    (ht : ∀ x, f (A.time x) = B.time (f x))
    (r : Fin B.period) (b : H) (hzero : f (A.point 0 1) = B.point r.val b) :
    ∃ m : ℕ, 0 < m ∧ A.period = B.period * m ∧
      b * B.holonomy ^ (m : ℤ) = A.holonomy * b ∧
      ∀ t z, f (A.point t z) = B.point (t + r.val) (z * b) := by
  obtain ⟨k, c, hk, _⟩ := seam_obstruction A B f hf ht
  have ha : (0 : ℤ) < A.period := by exact_mod_cast A.positive
  have hbpos : (0 : ℤ) < B.period := by exact_mod_cast B.positive
  have hkpos : 0 < k := by nlinarith
  let m := k.toNat
  have hmk : (m : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hkpos)
  have hdZ : (A.period : ℤ) = (B.period : ℤ) * (m : ℤ) := by rw [hmk]; exact hk
  have hd : A.period = B.period * m := by exact_mod_cast hdZ
  have hp := forward A B f hf ht hzero
  have seam : A.point (A.period : ℤ) 1 = A.point 0 A.holonomy :=
    (A.relation _ _ _ _).2 ⟨1, by omega, by simp⟩
  have out := congrArg f seam
  have hbase := hp 0 A.holonomy
  simp only [Nat.cast_zero, zero_add] at hbase
  rw [hp A.period 1, hbase] at out
  simp only [one_mul] at out
  obtain ⟨n, hn, hz⟩ := (B.relation _ _ _ _).1 out
  have hnm : n = (m : ℤ) := by nlinarith [hdZ]
  have hb : b * B.holonomy ^ (m : ℤ) = A.holonomy * b := by simpa [hnm] using hz
  refine ⟨m, by omega, hd, hb, ?_⟩
  intro t z
  let q := A.coordinates.symm (A.point t z)
  have he : A.point t z = A.point q.1.val q.2 := (A.coordinates.apply_symm_apply _).symm
  obtain ⟨n, hn, hz⟩ := (A.relation _ _ _ _).1 he
  rw [he, hp q.1.val q.2]
  symm
  apply (B.relation _ _ _ _).2
  refine ⟨(m : ℤ) * n, ?_, ?_⟩
  · rw [hdZ] at hn
    nlinarith only [hn]
  · have hc := SemiconjBy.zpow_right (show SemiconjBy b (B.holonomy ^ (m : ℤ)) A.holonomy from hb) n
    rw [← zpow_mul] at hc
    calc
      (z * b) * B.holonomy ^ ((m : ℤ) * n) = z * (b * B.holonomy ^ ((m : ℤ) * n)) := mul_assoc _ _ _
      _ = z * (A.holonomy ^ n * b) := congrArg (z * ·) hc
      _ = q.2 * b := by rw [← mul_assoc, hz]

/-- The degree and normalized image of the origin uniquely determine the signed map. -/
theorem normal_form (f : X → Y)
    (hf : ∀ a x, f (A.deck a x) = B.deck a (f x))
    (ht : ∀ x, f (A.time x) = B.time (f x)) :
    ∃! p : ℕ × (Fin B.period × H),
      0 < p.1 ∧ A.period = B.period * p.1 ∧
      p.2.2 * B.holonomy ^ (p.1 : ℤ) = A.holonomy * p.2.2 ∧
      ∀ t z, f (A.point t z) = B.point (t + p.2.1.val) (z * p.2.2) := by
  let q := B.coordinates.symm (f (A.point 0 1))
  have hq : f (A.point 0 1) = B.point q.1.val q.2 := (B.coordinates.apply_symm_apply _).symm
  obtain ⟨m, hm, hd, hb, law⟩ := anchored A B f hf ht q.1 q.2 hq
  refine ⟨(m,q), ⟨hm,hd,hb,law⟩, ?_⟩
  rintro ⟨n,r⟩ ⟨_,hn,_,hr⟩
  have hnm : n = m := Nat.eq_of_mul_eq_mul_left B.positive (hn.symm.trans hd)
  have hrq : r = q := B.coordinates.injective (by
    change B.point r.1.val r.2 = B.point q.1.val q.2
    simpa using (hr 0 1).symm.trans hq)
  exact Prod.ext hnm hrq

private theorem transport_signed (m : ℕ) (hd : A.period = B.period * m)
    (b : H) (hb : b * B.holonomy ^ (m : ℤ) = A.holonomy * b) (t : ℤ) (z : H) :
    transport A B b (A.point t z) = B.point t (z * b) := by
  let q := A.coordinates.symm (A.point t z)
  have he : A.point t z = A.point q.1.val q.2 := (A.coordinates.apply_symm_apply _).symm
  obtain ⟨n,hn,hz⟩ := (A.relation _ _ _ _).1 he
  change B.point q.1.val (q.2 * b) = B.point t (z * b)
  symm
  apply (B.relation _ _ _ _).2
  refine ⟨(m : ℤ) * n, ?_, ?_⟩
  · have hdZ : (A.period : ℤ) = (B.period : ℤ) * (m : ℤ) := by exact_mod_cast hd
    rw [hdZ] at hn
    nlinarith only [hn]
  · have hc := SemiconjBy.zpow_right (show SemiconjBy b (B.holonomy ^ (m : ℤ)) A.holonomy from hb) n
    rw [← zpow_mul] at hc
    calc
      (z * b) * B.holonomy ^ ((m : ℤ) * n) = z * (b * B.holonomy ^ ((m : ℤ) * n)) := mul_assoc _ _ _
      _ = z * (A.holonomy ^ n * b) := congrArg (z * ·) hc
      _ = q.2 * b := by rw [← mul_assoc,hz]

/-- Transport with an arbitrary normalized target phase. -/
def coveringMap (r : Fin B.period) (b : H) : X → Y :=
  fun x => B.time^[r.val] (transport A B b x)

private theorem coveringMap_point (m : ℕ) (hd : A.period = B.period * m)
    (r : Fin B.period) (b : H) (hb : b * B.holonomy ^ (m : ℤ) = A.holonomy * b)
    (t : ℤ) (z : H) :
    coveringMap A B r b (A.point t z) = B.point (t + r.val) (z * b) := by
  change B.time^[r.val] (transport A B b (A.point t z)) = _
  rw [transport_signed A B m hd b hb]
  have iter : ∀ n : ℕ, B.time^[n] (B.point t (z * b)) = B.point (t + n) (z * b) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, B.time_point]
      congr 1
      push_cast
      ring
  exact iter r.val

/-- Exact existence for a prescribed normalized seed, with no equal - period premise. -/
theorem map_criterion (r : Fin B.period) (b : H) :
    (∃ f : X → Y,
      (∀ a x, f (A.deck a x) = B.deck a (f x)) ∧
      (∀ x, f (A.time x) = B.time (f x)) ∧
      f (A.point 0 1) = B.point r.val b) ↔
    ∃ m : ℕ, 0 < m ∧ A.period = B.period * m ∧
      b * B.holonomy ^ (m : ℤ) = A.holonomy * b := by
  constructor
  · rintro ⟨f,hf,ht,hzero⟩
    obtain ⟨⟨m,q⟩,⟨hm,hd,hb,law⟩,_⟩ := normal_form A B f hf ht
    have hq : q = (r,b) := B.coordinates.injective (by
      change B.point q.1.val q.2 = B.point r.val b
      simpa using (law 0 1).symm.trans hzero)
    rw [hq] at hb
    exact ⟨m,hm,hd,hb⟩
  · rintro ⟨m,_,hd,hb⟩
    have law := coveringMap_point A B m hd r b hb
    refine ⟨coveringMap A B r b, ?_, ?_, ?_⟩
    · intro a x
      obtain ⟨t,z,rfl⟩ := A.covers x
      rw [A.deck_point,law,law,B.deck_point,mul_assoc]
    · intro x
      obtain ⟨t,z,rfl⟩ := A.covers x
      rw [A.time_point,law,law,B.time_point]
      congr 1
      omega
    · simpa using law 0 1

/-- The signed formula lands in the exact fiber over any target representative. -/
def fiberEnumeration (f : X → Y) (m : ℕ) (r : Fin B.period) (b : H)
    (law : ∀ t z, f (A.point t z) = B.point (t + r.val) (z * b))
    (s : ℤ) (w : H) (j : Fin m) : {x : X // f x = B.point s w} :=
  ⟨A.point (s - r.val + (B.period : ℤ) * j.val) (w * B.holonomy ^ (-(j.val : ℤ)) * b⁻¹), by
    rw [law]
    apply (B.relation _ _ _ _).2
    refine ⟨j.val, by omega, ?_⟩
    simp [mul_assoc]⟩

/-- Source seams identify two enumeration indices exactly modulo the degree;
Euclidean reduction of every signed target seam exhausts the fiber. -/
theorem fiberEnumeration_bijective (f : X → Y) (m : ℕ)
    (hd : A.period = B.period * m) (r : Fin B.period) (b : H)
    (hb : b * B.holonomy ^ (m : ℤ) = A.holonomy * b)
    (law : ∀ t z, f (A.point t z) = B.point (t + r.val) (z * b)) (s : ℤ) (w : H) :
    Function.Bijective (fiberEnumeration A B f m r b law s w) := by
  have hdZ : (A.period : ℤ) = (B.period : ℤ) * (m : ℤ) := by exact_mod_cast hd
  have hdpos : (0 : ℤ) < B.period := by exact_mod_cast B.positive
  have hm : 0 < m := by nlinarith [A.positive, B.positive]
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  constructor
  · intro j k he
    have he' := congrArg Subtype.val he
    obtain ⟨n,hn,_⟩ := (A.relation _ _ _ _).1 he'
    change s - r.val + (B.period : ℤ) * j.val =
      (s - r.val + (B.period : ℤ) * k.val) + (A.period : ℤ) * n at hn
    have heq : (j.val : ℤ) = (k.val : ℤ) + (m : ℤ) * n := by
      have hc : (B.period : ℤ) * (j.val : ℤ) = (B.period : ℤ) * ((k.val : ℤ) + (m : ℤ) * n) := by
        rw [hdZ] at hn
        nlinarith
      exact mul_left_cancel₀ (ne_of_gt hdpos) hc
    have hj : (j.val : ℤ) < m := by exact_mod_cast j.isLt
    have hk : (k.val : ℤ) < m := by exact_mod_cast k.isLt
    have hj0 := Int.natCast_nonneg j.val
    have hk0 := Int.natCast_nonneg k.val
    have hn0 : n = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hn | hn
      · have : n ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ n := by omega
        nlinarith
    apply Fin.ext
    exact_mod_cast (show (j.val : ℤ) = k.val by simpa [hn0] using heq)
  · rintro ⟨x,hx⟩
    obtain ⟨t,z,rfl⟩ := A.covers x
    rw [law] at hx
    obtain ⟨n,hn,hz⟩ := (B.relation _ _ _ _).1 hx
    let j : Fin m := ⟨(n % (m : ℤ)).toNat, by
      have := Int.emod_lt_of_pos n hmZ
      have := Int.emod_nonneg n (ne_of_gt hmZ)
      omega⟩
    have hj : (j.val : ℤ) = n % (m : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hmZ))
    let q : ℤ := n / (m : ℤ)
    have hnq : n = (j.val : ℤ) + (m : ℤ) * q := by
      dsimp [q]
      rw [hj]
      nlinarith only [Int.ediv_mul_add_emod n (m : ℤ)]
    refine ⟨j, Subtype.ext ?_⟩
    change A.point (s - r.val + (B.period : ℤ) * j.val)
      (w * B.holonomy ^ (-(j.val : ℤ)) * b⁻¹) = A.point t z
    symm
    apply (A.relation _ _ _ _).2
    refine ⟨q, ?_, ?_⟩
    · rw [hdZ]
      nlinarith [hnq]
    · have hc := SemiconjBy.zpow_right
        (show SemiconjBy b (B.holonomy ^ (m : ℤ)) A.holonomy from hb) q
      rw [← zpow_mul] at hc
      rw [zpow_neg]
      apply (eq_mul_inv_iff_mul_eq).2
      apply (eq_mul_inv_iff_mul_eq).2
      calc
        (z * A.holonomy ^ q) * b * B.holonomy ^ (j.val : ℤ) =
            z * (A.holonomy ^ q * b) * B.holonomy ^ (j.val : ℤ) := by group
        _ = z * (b * B.holonomy ^ ((m : ℤ) * q)) * B.holonomy ^ (j.val : ℤ) := by rw [hc]
        _ = (z * b) * B.holonomy ^ ((m : ℤ) * q + (j.val : ℤ)) := by rw [zpow_add]; group
        _ = w := by rw [show (m : ℤ) * q + (j.val : ℤ) = n by omega]; exact hz

/-- Every fiber has its full signed enumeration, using canonical target coordinates. -/
def fiberEquiv (f : X → Y) (m : ℕ) (hd : A.period = B.period * m)
    (r : Fin B.period) (b : H) (hb : b * B.holonomy ^ (m : ℤ) = A.holonomy * b)
    (law : ∀ t z, f (A.point t z) = B.point (t + r.val) (z * b))
    (y : Y) : Fin m ≃ {x : X // f x = y} := by
  let q := B.coordinates.symm y
  have hq : B.point q.1.val q.2 = y := B.coordinates.apply_symm_apply y
  let e := fiberEnumeration A B f m r b law q.1.val q.2
  have he := fiberEnumeration_bijective A B f m hd r b hb law q.1.val q.2
  exact Equiv.ofBijective (fun j => (⟨(e j).val, (e j).property.trans hq⟩ : {x // f x = y}))
    ⟨fun j k h => he.1 (Subtype.ext
      (congrArg (fun x : {x : X // f x = y} => x.val) h)), by
      intro x
      obtain ⟨j,hj⟩ := he.2 ⟨x.val,x.property.trans hq.symm⟩
      exact ⟨j,Subtype.ext
        (congrArg (fun x : {x : X // f x = B.point q.1.val q.2} => x.val) hj)⟩⟩

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ReturnAtlasFiniteCovers
