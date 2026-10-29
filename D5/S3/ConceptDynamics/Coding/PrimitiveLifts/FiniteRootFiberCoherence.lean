/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteRootFiberCoherence
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Finite or compact root fibers give rational coherence from positive roots. -/

import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.Tactic

open CategoryTheory Opposite

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteRootFiberCoherence

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

private structure PosDegree where
  val : ℕ+

private instance : LE PosDegree := ⟨fun a b => a.val ∣ b.val⟩

private instance : Preorder PosDegree where
  le_refl a := dvd_refl a.val
  le_trans a b c := dvd_trans

private instance : IsDirectedOrder PosDegree where
  directed a b := by
    refine ⟨⟨a.val * b.val⟩, ?_, ?_⟩
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _

private abbrev rootFiber {H : Type u} [Group H] (h : H) (n : PosDegree) :=
  {b : H // b ^ n.val.val = h}

private def quotient (m n : PosDegree) (hnm : n ≤ m) : ℕ+ :=
  PNat.divExact m.val n.val

private theorem quotient_spec {m n : PosDegree} (hnm : n ≤ m) :
    n.val * quotient m n hnm = m.val := by
  exact PNat.mul_div_exact hnm

private theorem quotient_comp {n m k : PosDegree} (hnm : n ≤ m) (hkm : m ≤ k) :
    quotient k m hkm * quotient m n hnm = quotient k n (le_trans hnm hkm) := by
  apply PNat.eq
  apply Nat.mul_left_cancel n.val.pos
  have hp : n.val * (quotient k m hkm * quotient m n hnm) =
      n.val * quotient k n (le_trans hnm hkm) := by
    calc
      n.val * (quotient k m hkm * quotient m n hnm) =
          (n.val * quotient m n hnm) * quotient k m hkm := by ac_rfl
      _ = m.val * quotient k m hkm := by rw [quotient_spec hnm]
      _ = k.val := quotient_spec hkm
      _ = n.val * quotient k n (le_trans hnm hkm) :=
        (quotient_spec (le_trans hnm hkm)).symm
  simpa using congrArg PNat.val hp

private theorem quotient_self (n : PosDegree) : quotient n n (le_refl n) = 1 := by
  apply PNat.eq
  apply Nat.mul_left_cancel n.val.pos
  have hp : n.val * quotient n n (le_refl n) = n.val * (1 : ℕ+) := by
    simpa using quotient_spec (le_refl n)
  simpa using congrArg PNat.val hp

private def rootMap {H : Type u} [Group H] {h : H} {m n : PosDegree}
    (hnm : n ≤ m) (x : rootFiber h m) : rootFiber h n :=
  ⟨x.1 ^ (quotient m n hnm).val, by
    rw [← pow_mul]
    have hpow : n.val.val * (quotient m n hnm).val = m.val.val := by
      simpa using congrArg PNat.val (quotient_spec hnm)
    have hpow' : (quotient m n hnm).val * n.val.val = m.val.val := by
      rw [Nat.mul_comm]
      exact hpow
    rw [hpow', x.2]⟩

private def rootSystem {H : Type u} [Group H] (h : H) : PosDegreeᵒᵖ ⥤ Type u where
  obj n := rootFiber h n.unop
  map f := ↾(fun x => rootMap (h := h) (leOfHom f.unop) x)
  map_id n := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext x
    apply Subtype.ext
    change (x.1 ^ (quotient n.unop n.unop (le_refl n.unop)).val : H) = x.1
    rw [quotient_self]
    exact pow_one x.1
  map_comp {X Y Z} f g := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext x
    apply Subtype.ext
    change x.1 ^ (quotient X.unop Z.unop _).val =
      (x.1 ^ (quotient X.unop Y.unop _).val) ^
        (quotient Y.unop Z.unop _).val
    rw [← pow_mul]
    have hxy : Y.unop ≤ X.unop := leOfHom f.unop
    have hyz : Z.unop ≤ Y.unop := leOfHom g.unop
    have hxz : Z.unop ≤ X.unop := le_trans hyz hxy
    have hqnat :
        (quotient X.unop Y.unop hxy).val * (quotient Y.unop Z.unop hyz).val =
          (quotient X.unop Z.unop hxz).val := by
      exact congrArg PNat.val (quotient_comp hyz hxy)
    rw [hqnat]

private theorem coherent_roots {H : Type u} [Group H] (h : H)
    (hfin : ∀ n : ℕ, 0 < n → Finite {b : H // b ^ n = h})
    (hex : ∀ n : ℕ, 0 < n → ∃ b : H, b ^ n = h) :
    ∃ (b : ∀ n : PosDegree, H),
      (∀ n : PosDegree, (b n) ^ n.val.val = h) ∧
        ∀ {n m : PosDegree} (hnm : n ≤ m),
          (b m) ^ (quotient m n hnm).val = b n := by
  let F := rootSystem h
  have hFfin : ∀ n : PosDegreeᵒᵖ, Finite (F.obj n) := by
    intro n
    dsimp [F, rootSystem, rootFiber]
    exact hfin n.unop.val.val n.unop.val.pos
  have hFne : ∀ n : PosDegreeᵒᵖ, Nonempty (F.obj n) := by
    intro n
    obtain ⟨b, hb⟩ := hex n.unop.val.val n.unop.val.pos
    dsimp [F, rootSystem, rootFiber]
    exact ⟨⟨b, hb⟩⟩
  letI : ∀ n : PosDegreeᵒᵖ, Finite (F.obj n) := hFfin
  letI : ∀ n : PosDegreeᵒᵖ, Nonempty (F.obj n) := hFne
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let chosen : ∀ n : PosDegree, rootFiber h n := fun n => s (op n)
  refine ⟨fun n => (chosen n).1, (fun n => (chosen n).2), ?_⟩
  intro n m hnm
  have hc := hs ((homOfLE hnm).op)
  dsimp [F, rootSystem] at hc
  have hc' : rootMap (h := h) hnm (s (op m)) = s (op n) := by
    exact hc
  simpa [chosen, rootMap] using congrArg Subtype.val hc'

private theorem rational_action_of_coherent_roots {H : Type u} [Group H] (h : H)
    (b : ∀ n : PosDegree, H)
    (hb : ∀ n : PosDegree, (b n) ^ n.val.val = h)
    (hcompat : ∀ {m n : PosDegree} (hnm : n ≤ m),
      (b m) ^ (quotient m n hnm).val = b n) :
    ∃ φ : Multiplicative ℚ →* H, φ (Multiplicative.ofAdd (1 : ℚ)) = h := by
  let degree : ℚ → PosDegree := fun q => ⟨⟨q.den, q.den_pos⟩⟩
  let common : PosDegree → PosDegree → PosDegree → PosDegree :=
    fun d e f => ⟨d.val * e.val * f.val⟩
  have hleft (d e f : PosDegree) : d ≤ common d e f := by
    change d.val ∣ d.val * e.val * f.val
    simpa [mul_assoc] using dvd_mul_right d.val (e.val * f.val)
  have hmid (d e f : PosDegree) : e ≤ common d e f := by
    change e.val ∣ d.val * e.val * f.val
    simpa [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_right e.val (d.val * f.val)
  have hright (d e f : PosDegree) : f ≤ common d e f := by
    change f.val ∣ d.val * e.val * f.val
    simpa [mul_assoc] using dvd_mul_left f.val (d.val * e.val)
  have qleft (d e f : PosDegree) :
      quotient (common d e f) d (hleft d e f) = e.val * f.val := by
    apply PNat.eq
    apply Nat.mul_left_cancel d.val.pos
    have hp : d.val * quotient (common d e f) d (hleft d e f) =
        d.val * (e.val * f.val) := by
      calc
        d.val * quotient (common d e f) d (hleft d e f) = (common d e f).val :=
          quotient_spec (hleft d e f)
        _ = d.val * (e.val * f.val) := by simp [common]; ac_rfl
    simpa using congrArg PNat.val hp
  have qmid (d e f : PosDegree) :
      quotient (common d e f) e (hmid d e f) = d.val * f.val := by
    apply PNat.eq
    apply Nat.mul_left_cancel e.val.pos
    have hp : e.val * quotient (common d e f) e (hmid d e f) =
        e.val * (d.val * f.val) := by
      calc
        e.val * quotient (common d e f) e (hmid d e f) = (common d e f).val :=
          quotient_spec (hmid d e f)
        _ = e.val * (d.val * f.val) := by simp [common]; ac_rfl
    simpa using congrArg PNat.val hp
  have qright (d e f : PosDegree) :
      quotient (common d e f) f (hright d e f) = d.val * e.val := by
    apply PNat.eq
    apply Nat.mul_left_cancel f.val.pos
    have hp : f.val * quotient (common d e f) f (hright d e f) =
        f.val * (d.val * e.val) := by
      calc
        f.val * quotient (common d e f) f (hright d e f) = (common d e f).val :=
          quotient_spec (hright d e f)
        _ = f.val * (d.val * e.val) := by simp [common]; ac_rfl
    simpa using congrArg PNat.val hp
  let value : ℚ → H := fun q => (b (degree q)) ^ q.num
  have value_zero : value 0 = 1 := by simp [value, degree]
  have value_add (q r : ℚ) : value (q + r) = value q * value r := by
    let d := degree q
    let e := degree r
    let f := degree (q + r)
    let c := common d e f
    have hqd := hcompat (hleft d e f)
    have hrd := hcompat (hmid d e f)
    have hsd := hcompat (hright d e f)
    have hq : value q = (b c) ^
        (((e.val.val * f.val.val : ℕ) : ℤ) * q.num) := by
      dsimp [value, d, e, f, c]
      rw [← hqd, ← zpow_natCast, ← zpow_mul]
      rw [qleft]
      simp [d, e, f, c]
    have hr : value r = (b c) ^
        (((d.val.val * f.val.val : ℕ) : ℤ) * r.num) := by
      dsimp [value, d, e, f, c]
      rw [← hrd, ← zpow_natCast, ← zpow_mul]
      rw [qmid]
      simp [d, e, f, c]
    have hs : value (q + r) = (b c) ^
        (((d.val.val * e.val.val : ℕ) : ℤ) * (q + r).num) := by
      dsimp [value, d, e, f, c]
      rw [← hsd, ← zpow_natCast, ← zpow_mul]
      rw [qright]
      simp [d, e, f, c]
    rw [hq, hr, hs, ← zpow_add]
    congr 1
    have hn := Rat.add_num_den' q r
    change ((d.val.val * e.val.val : ℕ) : ℤ) * (q + r).num =
        ((e.val.val * f.val.val : ℕ) : ℤ) * q.num +
          ((d.val.val * f.val.val : ℕ) : ℤ) * r.num
    rw [add_mul] at hn
    simpa [d, e, f, degree, mul_assoc, mul_comm, mul_left_comm] using hn
  let χ : AddChar ℚ H :=
    { toFun := value
      map_zero_eq_one' := value_zero
      map_add_eq_mul' := value_add }
  refine ⟨χ.toMonoidHom, ?_⟩
  simpa [χ, value, degree] using hb (degree 1)

/-- For any group H and fixed h with finite positive-degree root fibers, independent roots
in every positive degree are equivalent to a monoid homomorphism φ : Multiplicative ℚ →* H
with φ (Multiplicative.ofAdd (1 : ℚ)) = h. -/
theorem finite_root_fibers_rational_coherence {H : Type u} [Group H] (h : H)
    (hfin : ∀ n : ℕ, 0 < n → Finite {b : H // b ^ n = h}) :
    (∀ n : ℕ, 0 < n → ∃ b : H, b ^ n = h) ↔
      ∃ φ : Multiplicative ℚ →* H, φ (Multiplicative.ofAdd (1 : ℚ)) = h := by
  constructor
  · intro hex
    obtain ⟨b, hb, hcompat⟩ := coherent_roots h hfin hex
    exact rational_action_of_coherent_roots h b hb hcompat
  · rintro ⟨φ, hφ⟩ n hn
    refine ⟨φ (Multiplicative.ofAdd (1 / n : ℚ)), ?_⟩
    have hp := φ.map_pow (Multiplicative.ofAdd (1 / n : ℚ)) n
    have hx : (Multiplicative.ofAdd (1 / n : ℚ)) ^ n =
        Multiplicative.ofAdd (1 : ℚ) := by
      change Multiplicative.ofAdd (n • (1 / n : ℚ)) = Multiplicative.ofAdd (1 : ℚ)
      congr 1
      norm_num [nsmul_eq_mul, hn.ne']
    rw [hx, hφ] at hp
    exact hp.symm

#print axioms finite_root_fibers_rational_coherence

private def topologicalRootSystem {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (h : H) : PosDegreeᵒᵖ ⥤ TopCat.{u} where
  obj n := TopCat.of (rootFiber h n.unop)
  map f := TopCat.ofHom
    { toFun := rootMap (h := h) (leOfHom f.unop)
      continuous_toFun := (continuous_subtype_val.pow _).subtype_mk _ }
  map_id n := by
    ext x
    exact congrArg Subtype.val
      (congrFun (congrArg (fun f => f.hom) ((rootSystem h).map_id n)) x)
  map_comp f g := by
    ext x
    exact congrArg Subtype.val
      (congrFun (congrArg (fun f => f.hom) ((rootSystem h).map_comp f g)) x)

/-- Compact positive-degree root fibers in the actual topology of a Hausdorff topological
group suffice for algebraic rational coherence. Neither the ambient group nor the root
fibers need be finite, and no continuity of the resulting homomorphism is asserted. -/
theorem compact_root_fibers_rational_coherence {H : Type u} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (h : H)
    (hcompact : ∀ n : ℕ, 0 < n → IsCompact {x : H | x ^ n = h}) :
    (∀ n : ℕ, 0 < n → ∃ x : H, x ^ n = h) ↔
      ∃ φ : Multiplicative ℚ →* H, φ (Multiplicative.ofAdd (1 : ℚ)) = h := by
  constructor
  · intro hex
    let F := topologicalRootSystem h
    haveI : ∀ n : PosDegreeᵒᵖ, CompactSpace (F.obj n) := fun n => by
      change CompactSpace {x : H // x ^ n.unop.val.val = h}
      exact isCompact_iff_compactSpace.mp (hcompact n.unop.val.val n.unop.val.pos)
    haveI : ∀ n : PosDegreeᵒᵖ, T2Space (F.obj n) := fun n => by
      change T2Space {x : H // x ^ n.unop.val.val = h}
      infer_instance
    haveI : ∀ n : PosDegreeᵒᵖ, Nonempty (F.obj n) := fun n => by
      change Nonempty {x : H // x ^ n.unop.val.val = h}
      obtain ⟨x, hx⟩ := hex n.unop.val.val n.unop.val.pos
      exact ⟨⟨x, hx⟩⟩
    obtain ⟨s⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system F
    apply rational_action_of_coherent_roots h (fun n => (s.val (op n)).val)
      (fun n => (s.val (op n)).property)
    intro m n hnm
    exact congrArg Subtype.val (s.property (homOfLE hnm).op)
  · rintro ⟨φ, hφ⟩ n hn
    refine ⟨φ (Multiplicative.ofAdd (1 / n : ℚ)), ?_⟩
    have hp := φ.map_pow (Multiplicative.ofAdd (1 / n : ℚ)) n
    have hx : (Multiplicative.ofAdd (1 / n : ℚ)) ^ n =
        Multiplicative.ofAdd (1 : ℚ) := by
      change Multiplicative.ofAdd (n • (1 / n : ℚ)) = Multiplicative.ofAdd (1 : ℚ)
      congr 1
      norm_num [nsmul_eq_mul, hn.ne']
    rw [hx, hφ] at hp
    exact hp.symm

#print axioms compact_root_fibers_rational_coherence

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteRootFiberCoherence
