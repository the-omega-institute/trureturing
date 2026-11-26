import OmegaMath.NumberTheory.GRH.Lib.ClassField.Global.CMNorms
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Landherr's Hasse principle for hermitian forms; weak approximation for unitary groups
(known result; see Lib.Adelic.Landherr.Landherr).

This file: A totally positive element is a sum of two squares in a quadratic algebra, via
Hasse's norm theorem. -/

open Algebra QuadraticAlgebra Set NumberField

/-- Let E satisfy `StablyUnram`, S be a set of finite places of E, and p, q, B ∈ E⁺, p ≠ 0 totally
positive, p a unit outside S, q a unit on S ∪ S̄. Then p = x² + y² is solvable in E⁺[X]/(X²
− (qp − B²)). -/
lemma exists_sq_add_sq_quadraticAlgebra {E} [Field.{0} E] [CMType E] [StablyUnram E] (p q B :
  maximalRealSubfield E) {S : Set (FinPlace E)} (t : IsTotallyPositive p) (a : ∀ w ∉ S,
  w.valuation E p = 1) (c : ∀ w ∈ S.conjClosure, w.valuation E q =
  1) : ∃ z : QuadraticAlgebra (QuadraticAlgebra _ (q * p - B ^ 2) 0) (-1) 0, z.norm = ⟨p, 0⟩ := by
  set μ := _ - B ^ 2
  have H {M} [Field M] [NumberField M] (i : _ →+* M) m (h : m * m = i μ) :
      ∃ z : QuadraticAlgebra M (-1) 0, z.norm = i p := ?_ <;> by_contra k
  let := @instField _ _ μ 0 ⟨fun r e ↦ have ⟨⟨x, y⟩, _⟩ := H 1 r (by simp_all [sq])
    k ⟨⟨.C x, .C y⟩, by ext <;> simp_all [norm_def]⟩⟩
  exact k (@H _ _ (.of_module_finite (type_of% p) _) (algebraMap ..) _ omega_mul_omega_eq_mk)
  let := @instField M _ (-1) 0 ⟨fun r e ↦ k ⟨⟨i p + 4⁻¹, (i p - 4⁻¹) / r⟩, by grind [norm_def]⟩⟩
  have := IsQuadraticExtension.mk (finrank_eq_two (-1 : M) 0)
  have n z : norm M z = _ := @det_toLinearMap_eq_norm M _ (-1) 0 z
  refine (@hasse_norm _ _ _ _ _ _ _ (of_module_finite M _) _ (.mk0 _ (k ⟨0, by simp [·]⟩))
    (fun w ↦ ?_) (t <| ·.comp i)).elim (k ⟨·.1, n _ ▸ congr($(·).1)⟩)
  obtain ⟨⟨I, _⟩, ⟨u, o⟩, y, e⟩ := ‹StablyUnram E›.exists_i_c₀, (w.comap i).comap_surjective
    (algebraMap _ E), exists_norm_eq_Ô (u := ((q⁻¹ - p) * idem S.conjClosure + p :))
    (by simp [mem_maximalRealSubfield_iff_star_eq.1]) (by aesop (add simp idem_apply))
  let T x := trace (type_of% p) E (x / 2)
  let z := ite (u ∈ S.conjClosure) (@mk M (-1) 0 (i B) m) 1
  exact mem_of_eq_of_mem (by simp [← map_mul]; by_cases q = 0 <;> split <;> simp_all [z, μ,
    norm_def, field]) (map_mem_closure ((continuous_locMap i rfl).const_mul (algebraMap M _ z.norm))
    (((locMap _ o).injective (by split <;> simp [*, -map_inv₀, ← adeleMap_apply,
    finAdeleIncl_adeleNorm_eq_mul_star] <;> rfl) : adeleNorm _ E (star y) _ =
    algebraMap _ _ (ite (u ∈ S.conjClosure) q⁻¹ p)) ▸ adeleNorm_mem_closure) (by
    rintro _ ⟨x, rfl⟩; use z * ⟨i (T x), i (T (x * I))⟩; simp [n, norm_def, show norm _ x = T x ^ 2
   + T (x * I) ^ 2 by ext; simp_all [T, trace_maximalReal_eq_add_star,
      norm_maximalRealSubfield_eq_mul_star, RingOfIntegers.ext_iff]; grind]; ring))
