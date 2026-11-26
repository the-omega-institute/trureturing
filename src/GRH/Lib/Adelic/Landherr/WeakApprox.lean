import GRH.Lib.Adelic.Adeles.MatrixApprox
import GRH.Lib.Adelic.Reduction.MinkowskiSecond
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Landherr's Hasse principle for hermitian forms; weak approximation for unitary groups
(known result; see Lib.Adelic.Landherr.Landherr).

This file: Weak approximation for unitary groups over CM fields by a Cayley-type transform. -/

namespace Space

open Matrix Topology Filter G Function Gf RingHom Algebra
variable {E n : Type*} [Field E] [CMType E] [Fintype n] {s} (V : Space E n s)

instance : Infinite (unitary E) := exists_isUnit_sub_star.elim fun z _ ↦ .of_injective ((fun y ↦ ⟨1
  - (y - star y) * y⁻¹, by simp [unitary]; grind [star_eq_zero]⟩) ∘ (Nat.cast · + z)) (by aesop_cat)

/-- A Cayley-type map: for c c̄ = 1 and A over E, the image in G of the J-unitary matrix A +
(c⁻¹−A)(1−Q⁻¹N), where N = (c−Aᴴ)J, Q = N + (c/2)(AᴴJA−J), and Q⁻¹ = 0 for singular Q. -/
noncomputable def cayleyMap (c : unitary E) A := let N := (c.1 • 1 - Aᴴ) * V.J
  let Q := N + (c.1 / 2) • (Aᴴ * V.J * A - V.J)
  V.ratEmbed (U.of V.isUnit_J (A + (c.1⁻¹ • 1 - A) * (1 - Q⁻¹ * N)) (by
    have k : c.1 • ((Q * Q⁻¹)ᴴ - 1) * Q⁻¹ = 0 := by cases Q.nonsing_inv_cancel_or_zero <;> aesop
    linear_combination (norm := simp [Q, N, conjTranspose_J]) congr(Nᴴ * ($k + $kᴴ) * N)
    noncomm_ring; match_scalars <;> clear * - <;> grind [c.2.1]))

lemma eventually_tendsto_cayleyMap g e {K} [NormedField K] (f : _ →+* K) (t : Continuous f) (h :
  f e = 0 ∧ f (star e) = 0) : ∀ᶠ c in cofinite, Tendsto (V.cayleyMap c ·.1 |>.mat.map f)
  (comap (fun p ↦ p.1.map toAdele + e • Prod.snd p) (𝓝 (V.toRatCoords g)))
  (𝓝 (g.mat.map f)) := let φ := f.comp toAdele; .mono (φ.injective.injOn.injective.tendsto_cofinite
    ((V.toRatCoords g).1.1ᴴ.map f).finite_spectrum) fun c d ↦ by
    rcases (d.mul (V.isUnit_J.map φ.mapMatrix)).map detMonoidHom, congr(map $((V.toRatCoords g).2)
      f)
    convert (?_ :
      ContinuousAt (uncurry ?G ∘ fun x ↦ (map x f, xᴴ.map f)) _).tendsto.comp map_comap_le
    simp [mat_ratEmbed, cayleyMap, map_det, @inv_def _ E, ← coe_comp, ← f.comp_apply, φ, map_smul',
      Matrix.map_sub, φ.map_adjugate, ← φ.mapMatrix_apply (adjugate _), Matrix.map_add, *]
    generalize map _ φ = x, map _ φ = y; rfl
    all_goals simp_all [φ, adjugate_mul, -det_mul, algebraMap_eq_smul_one]
    simp [mul_assoc, ← Matrix.map_mul, toRatCoords, mat]
    fun_prop (disch := aesop)

/-- Weak approximation for U(J): for a finite set S of finite places, a neighbourhood O of 1 in
G and g in G, some rational γ has γg = hu with u in O and h in G_f trivial at S.

Known result: Landherr's Hasse principle for hermitian forms; weak approximation for unitary
groups. -/
lemma weak_approximation {S} (hS : S.Finite) : DenseRange fun p : V.Γ × trivialOn n S ↦ p.1.1 * (1,
  p.2.1) := fun g ↦ ((eventually_all.2 fun w ↦ V.eventually_tendsto_cayleyMap g (idemAdele
  S.conjClosureᶜ) _ (continuous_apply w).fst' (by simp)).and (hS.cj.toFinset.eventually_all.2 fun w
  _ ↦ V.eventually_tendsto_cayleyMap g (idemAdele S.conjClosureᶜ) ((evalAt w).comp (snd ..))
  (continuous_evalAt w).snd' (by aesop))).exists.elim fun c h ↦ let π := Prod.map id (componentOn n
    S); mul_inv_cancel_left (π g) g ▸ mem_closure_of_frequently_of_tendsto (@.of_forall _ _
    (comap_neBot fun _ ↦ by simpa using! (denseRange_rat_matrix_add hS.cj.exists_notMem 1).mem_nhds)
    _ (let x := V.cayleyMap c ·.1; ⟨(⟨x, _, rfl⟩, ⟨(x⁻¹ * π (x * g⁻¹) * g).2, by aesop⟩), by
      aesop⟩)) (.mul_const _ (isClosedEmbedding_mat.tendsto_nhds_iff (g := π ∘ V.cayleyMap c ∘ _).2
    (tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ .prodMk_nhds (tendsto_pi_nhds.2
    (h.1 · |>.apply_nhds i |>.apply_nhds j)) (.add_const _ (by convert tendsto_finsetSum _ (.comp
    (continuous_singleAdele _).continuousAt <| h.2 · · |>.apply_nhds i
    |>.apply_nhds j) <;> ext <;> erw [map_sum (evalAt _), Finset.sum_pi_single] <;> aesop)))))
