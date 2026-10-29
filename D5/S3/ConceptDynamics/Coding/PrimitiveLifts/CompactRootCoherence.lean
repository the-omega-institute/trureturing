/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/CompactRootCoherence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/CompactRootCoherence
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: In a compact Hausdorff topological group, independent positive roots exist iff one rational homomorphism sends additive rational one to the element. -/

import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Floor
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Tactic

/-! Compactness turns separate positive roots in a compact Hausdorff group into one coherent
rational homomorphism. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.CompactRootCoherence

private theorem rat_nat_mul_is_int {q : ℚ} {D : ℕ} (hD : q.den ∣ D) :
    ∃ z : ℤ, (D : ℚ) * q = z := by
  rcases hD with ⟨k, rfl⟩
  refine ⟨(k : ℤ) * q.num, ?_⟩
  calc
    ((q.den * k : ℕ) : ℚ) * q = (k : ℚ) * ((q.den : ℚ) * q) := by
      push_cast
      ring
    _ = (k : ℚ) * q.num := by rw [Rat.den_mul_eq_num]
    _ = (((k : ℤ) * q.num : ℤ) : ℚ) := by norm_num

private theorem floor_nat_mul_add {p q : ℚ} {D : ℕ}
    (hp : p.den ∣ D) (hq : q.den ∣ D) :
    ⌊(D : ℚ) * (p + q)⌋ = ⌊(D : ℚ) * p⌋ + ⌊(D : ℚ) * q⌋ := by
  obtain ⟨zp, hpz⟩ := rat_nat_mul_is_int hp
  obtain ⟨zq, hqz⟩ := rat_nat_mul_is_int hq
  have hpFloor : ⌊(D : ℚ) * p⌋ = zp := by rw [hpz, Int.floor_intCast]
  have hqFloor : ⌊(D : ℚ) * q⌋ = zq := by rw [hqz, Int.floor_intCast]
  calc
    ⌊(D : ℚ) * (p + q)⌋ = ⌊(D : ℚ) * p + (D : ℚ) * q⌋ := by rw [mul_add]
    _ = ⌊(zp : ℚ) + (zq : ℚ)⌋ := by rw [hpz, hqz]
    _ = zp + zq := by rw [← Int.cast_add, Int.floor_intCast]
    _ = ⌊(D : ℚ) * p⌋ + ⌊(D : ℚ) * q⌋ := by rw [hpFloor, hqFloor]

/-- Separate positive roots are coherent exactly when they arise from one rational homomorphism. -/
theorem exists_all_positive_roots_iff_exists_rat_hom
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [CompactSpace H] (h : H) :
    (∀ n : ℕ, 0 < n → ∃ x : H, x ^ n = h) ↔
      ∃ φ : Multiplicative ℚ →* H, φ (Multiplicative.ofAdd 1) = h := by
  constructor
  · intro rootHyp
    let C : Finset ℚ → Set (ℚ → H) := fun S =>
      {F | F 0 = 1 ∧ F 1 = h ∧ ∀ p ∈ S, ∀ q ∈ S, F (p + q) = F p * F q}
    have hCclosed (S : Finset ℚ) : IsClosed (C S) := by
      have hset : C S = ({F : ℚ → H | F 0 = 1} ∩
          ({F : ℚ → H | F 1 = h} ∩
            ⋂ p ∈ S, ⋂ q ∈ S, {F : ℚ → H | F (p + q) = F p * F q})) := by
        ext F
        simp [C]
      rw [hset]
      exact (isClosed_eq (continuous_apply 0) continuous_const).inter <|
        (isClosed_eq (continuous_apply 1) continuous_const).inter <|
          isClosed_biInter fun p hp => isClosed_biInter fun q hq =>
            isClosed_eq (continuous_apply (p + q))
              ((continuous_apply p).mul (continuous_apply q))
    have hCcompact (S : Finset ℚ) : IsCompact (C S) := (hCclosed S).isCompact
    have hCdirected : Directed (· ⊇ ·) C := by
      intro S T
      refine ⟨S ∪ T, ?_, ?_⟩
      · intro F hF
        exact ⟨hF.1, hF.2.1, fun p hp q hq =>
          hF.2.2 p (Finset.mem_union_left T hp) q (Finset.mem_union_left T hq)⟩
      · intro F hF
        exact ⟨hF.1, hF.2.1, fun p hp q hq =>
          hF.2.2 p (Finset.mem_union_right S hp) q (Finset.mem_union_right S hq)⟩
    have hCnonempty : ∀ S, (C S).Nonempty := by
      intro S
      let D : ℕ := ∏ q ∈ S, q.den
      have hD : 0 < D := by
        dsimp [D]
        exact Finset.prod_pos fun q hq => Rat.pos q
      have hden (q : ℚ) (hq : q ∈ S) : q.den ∣ D := by
        exact Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hq
      obtain ⟨x, hx⟩ := rootHyp D hD
      let F : ℚ → H := fun q => x ^ ⌊(D : ℚ) * q⌋
      have hF0 : F 0 = 1 := by simp [F]
      have hF1 : F 1 = h := by simpa [F] using hx
      have hFadd (p q : ℚ) (hp : p ∈ S) (hq : q ∈ S) :
          F (p + q) = F p * F q := by
        dsimp [F]
        rw [floor_nat_mul_add (hden p hp) (hden q hq), zpow_add]
      exact ⟨F, ⟨hF0, hF1, fun p hp q hq => hFadd p q hp hq⟩⟩
    obtain ⟨F, hF⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      C hCdirected hCnonempty hCcompact hCclosed
    have hFS (S : Finset ℚ) : F ∈ C S := Set.mem_iInter.mp hF S
    have h0 : F 0 = 1 := (hFS ∅).1
    have h1 : F 1 = h := (hFS ∅).2.1
    have hadd (p q : ℚ) : F (p + q) = F p * F q := by
      have hpq := hFS {p, q}
      exact hpq.2.2 p (by simp) q (by simp)
    let A : ℚ →+ Additive H :=
      { toFun := fun q => Additive.ofMul (F q)
        map_zero' := by simpa [h0]
        map_add' := by intro p q; exact congrArg Additive.ofMul (hadd p q) }
    let φ : Multiplicative ℚ →* H := AddMonoidHom.toMultiplicativeLeft A
    refine ⟨φ, ?_⟩
    change (A 1).toMul = h
    simpa [A, h1]
  · rintro ⟨φ, hφ⟩ n hn
    refine ⟨φ (Multiplicative.ofAdd (1 / (n : ℚ))), ?_⟩
    calc
      φ (Multiplicative.ofAdd (1 / (n : ℚ))) ^ n =
          φ ((Multiplicative.ofAdd (1 / (n : ℚ))) ^ n) :=
        (φ.map_pow _ _).symm
      _ = φ (Multiplicative.ofAdd 1) := by
        apply congrArg φ
        apply Multiplicative.ofAdd.injective
        change n • (1 / (n : ℚ)) = (1 : ℚ)
        rw [nsmul_eq_mul]
        field_simp [Nat.ne_of_gt hn]
      _ = h := hφ

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.CompactRootCoherence
