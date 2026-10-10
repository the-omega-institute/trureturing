/- GID: D5/S3/Geometry/FiniteGeometry/SingerTracePlane
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/SingerTracePlane
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic finite-field trace planes yield Singer difference sets and their doubles. -/

/-
proof_shape: no_proper_invariant_subspace, trace_plane_intersection, result: content.
escape_witness: the multiplier-preserving subalgebra constructed in
  no_proper_invariant_subspace; trace_plane_intersection uses it to distinguish
  the two trace planes and establish their one-dimensional intersection.
admission_basis: escape-witness
Direct frozen dependencies: none; only pinned Mathlib is imported.
Information-escape registration is paused under CLAUDE.md section 3.9.
Private helper classification: projective_bijective, count_submodule, singer_card,
  singer_difference, quadric_card and quadric_difference are content; all other
  private theorems are bind-only with consumers on the path to result.
-/

import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Projectivization.Cardinality

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace D5.S3.Geometry.FiniteGeometry.SingerTracePlane

variable {p : ℕ} [Fact p.Prime]

theorem no_proper_invariant_subspace (a : GaloisField p 3)
    (ha : a ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)))
    (W : Submodule (ZMod p) (GaloisField p 3))
    (hinv : ∀ x ∈ W, a*x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let S : Subalgebra (ZMod p) (GaloisField p 3) :=
    { carrier := {b | ∀ x ∈ W, b*x ∈ W}
      mul_mem' := by
        intro b c hb hc x hx
        simpa only [mul_assoc] using hb (c*x) (hc x hx)
      add_mem' := by
        intro b c hb hc x hx
        simpa only [add_mul] using W.add_mem (hb x hx) (hc x hx)
      one_mem' := by intro x hx; simpa using hx
      zero_mem' := by intro x hx; simpa using W.zero_mem
      algebraMap_mem' := by
        intro c x hx
        simpa only [Algebra.smul_def] using W.smul_mem c hx }
  have hs : S ≠ ⊥ := by
    intro h
    have hm : a ∈ S := hinv
    rw [h] at hm
    exact ha hm
  letI := Subalgebra.isSimpleOrder_of_finrank_prime (ZMod p) (GaloisField p 3)
    (by rw [GaloisField.finrank p (by decide : 3 ≠ 0)]; exact Nat.prime_three)
  have ht : S = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top S).resolve_left hs
  by_cases hw : W = ⊥
  · exact Or.inl hw
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
    apply top_unique
    intro x _
    have hm : x/v ∈ S := by rw [ht]; trivial
    simpa only [div_mul_cancel₀ _ hv0] using hm v hv

private theorem kernel_finrank (f : GaloisField p 3 →ₗ[ZMod p] ZMod p)
    (hf : Function.Surjective f) : finrank (ZMod p) f.ker = 2 := by
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, finrank_self,
    GaloisField.finrank p (by decide : 3 ≠ 0)] at h
  omega

theorem trace_plane_intersection (a : GaloisField p 3)
    (hbase : a ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3))) :
    finrank (ZMod p) ↥((Algebra.trace (ZMod p) (GaloisField p 3)).ker ⊓
      ((Algebra.trace (ZMod p) (GaloisField p 3)).comp
        (LinearMap.mulLeft (ZMod p) a)).ker) = 1 := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hbase ⟨0, map_zero _⟩
  let T := Algebra.trace (ZMod p) (GaloisField p 3)
  let U := T.comp (LinearMap.mulLeft (ZMod p) a)
  have hT : finrank (ZMod p) T.ker = 2 :=
    kernel_finrank T (Algebra.trace_surjective _ _)
  have hU : finrank (ZMod p) U.ker = 2 := by
    apply kernel_finrank
    intro c
    obtain ⟨x, hx⟩ := Algebra.trace_surjective (ZMod p) (GaloisField p 3) c
    refine ⟨a⁻¹*x, ?_⟩
    simpa [U, T, mul_assoc, ha] using hx
  have hne : T.ker ≠ U.ker := by
    intro he
    have hi : ∀ x ∈ T.ker, a*x ∈ T.ker := by
      intro x hx
      rw [he] at hx
      exact hx
    rcases no_proper_invariant_subspace a hbase T.ker hi with hb | ht
    · rw [hb, finrank_bot] at hT; omega
    · rw [ht, finrank_top, GaloisField.finrank p (by decide : 3 ≠ 0)] at hT; omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq T.ker U.ker
  have hup : finrank (ZMod p) ↥(T.ker ⊔ U.ker) ≤ 3 := by
    simpa [GaloisField.finrank p (by decide : 3 ≠ 0)] using
      (T.ker ⊔ U.ker).finrank_le
  have hlo : 2 < finrank (ZMod p) ↥(T.ker ⊔ U.ker) := by
    by_contra! h
    have he := Submodule.eq_of_le_of_finrank_le
      (show T.ker ≤ T.ker ⊔ U.ker from le_sup_left) (by omega)
    have hf := Submodule.eq_of_le_of_finrank_le
      (show U.ker ≤ T.ker ⊔ U.ker from le_sup_right) (by omega)
    exact hne (he.trans hf.symm)
  change finrank (ZMod p) ↥(T.ker ⊓ U.ker) = 1
  omega

private theorem norm_power (α : GaloisField p 3) :
    algebraMap (ZMod p) (GaloisField p 3) (Algebra.norm (ZMod p) α) = α ^ (p ^ 2 + p + 1) := by
  have h := FiniteField.algebraMap_norm_eq_pow_sum (ZMod p) (GaloisField p 3) α
  simpa [GaloisField.finrank p (by decide : 3 ≠ 0), Nat.card_zmod,
    Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using h

private theorem trace_nonzero_scaled (α : GaloisField p 3) (hα : α ≠ 0) (x : GaloisField p 3) :
    Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (p ^ 2 + p + 1) * x) = 0 ↔
      Algebra.trace (ZMod p) (GaloisField p 3) x = 0 := by
  have hn : Algebra.norm (ZMod p) α ≠ 0 := by
    intro h
    have hp := norm_power α
    rw [h, map_zero] at hp
    exact pow_ne_zero _ hα hp.symm
  rw [← norm_power α, ← Algebra.smul_def, map_smul, smul_eq_mul]
  exact mul_eq_zero.trans (or_iff_right hn)

private theorem trace_periodic (α : GaloisField p 3) (hα : α ≠ 0) (i : ℕ) :
    Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (i + (p ^ 2 + p + 1))) = 0 ↔
      Algebra.trace (ZMod p) (GaloisField p 3) (α ^ i) = 0 := by
  rw [pow_add, mul_comm]
  exact trace_nonzero_scaled α hα _

private theorem trace_mod (α : GaloisField p 3) (hα : α ≠ 0) (i : ℕ) :
    Algebra.trace (ZMod p) (GaloisField p 3) (α ^ i) = 0 ↔
      Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (i % (p ^ 2 + p + 1))) = 0 := by
  have he : ∀ j r : ℕ,
      Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (r + (p ^ 2 + p + 1) * j)) = 0 ↔
        Algebra.trace (ZMod p) (GaloisField p 3) (α ^ r) = 0 := by
    intro j r
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, ← add_assoc, trace_periodic α hα]
      exact ih
  conv_lhs => rw [← Nat.mod_add_div i ((p ^ 2 + p + 1))]
  exact he _ _


private theorem primitive_ne_zero (α : GaloisField p 3) (hα : orderOf α = p^3-1) : α ≠ 0 := by
  intro hz
  have hp := (Fact.out : p.Prime).two_le
  rw [hz, orderOf_zero] at hα
  have hpow : 8 ≤ p^3 := Nat.pow_le_pow_left hp 3
  omega

private theorem primitive_bijective (α : GaloisField p 3) (hα : orderOf α = p^3-1) :
    Function.Bijective (fun i : Fin (p^3-1) =>
      Units.mk0 (α^i.val) (pow_ne_zero _ (primitive_ne_zero α hα))) := by
  letI := Fintype.ofFinite (GaloisField p 3)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hh : α^i.val = α^j.val := congrArg Units.val hij
    have ho : IsOfFinOrder α := orderOf_pos_iff.mp (by rw [hα]; have hp := (Fact.out : p.Prime).two_le; have hh : 8 ≤ p^3 := Nat.pow_le_pow_left hp 3; omega)
    have hh' := ho.pow_inj_mod.mp hh
    rw [hα, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hh'
    exact Fin.ext hh'
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_units,
      GaloisField.card p 3 (by decide)]

private theorem projective_mod (α : GaloisField p 3) (hα : α ≠ 0) (i : ℕ) :
    Projectivization.mk (ZMod p) (α^i) (pow_ne_zero _ hα) =
      Projectivization.mk (ZMod p) (α^(i % (p ^ 2 + p + 1))) (pow_ne_zero _ hα) := by
  apply (Projectivization.mk_eq_mk_iff' (ZMod p) _ _ _ _).mpr
  refine ⟨Algebra.norm (ZMod p) α ^ (i / (p ^ 2 + p + 1)), ?_⟩
  rw [Algebra.smul_def, map_pow, norm_power, ← pow_mul, ← pow_add]
  congr 1
  exact (Nat.add_comm _ _).trans (Nat.mod_add_div i ((p ^ 2 + p + 1)))

private theorem projective_bijective (α : GaloisField p 3) (hα : orderOf α = p^3-1) :
    Function.Bijective (fun i : Fin (p ^ 2 + p + 1) =>
      Projectivization.mk (ZMod p) (α^i.val) (pow_ne_zero _ (primitive_ne_zero α hα))) := by
  letI := Fintype.ofFinite (Projectivization (ZMod p) (GaloisField p 3))
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro P
    obtain ⟨i, hi⟩ := (primitive_bijective α hα).2 (Units.mk0 P.rep P.rep_nonzero)
    refine ⟨⟨i.val % (p ^ 2 + p + 1), Nat.mod_lt _ (NeZero.pos _)⟩, ?_⟩
    have hh : α^i.val = P.rep := congrArg Units.val hi
    change Projectivization.mk (ZMod p) (α^(i.val % (p ^ 2 + p + 1))) _ = P
    rw [← projective_mod α (primitive_ne_zero α hα)]
    simpa only [hh, Projectivization.mk_rep]
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
      Projectivization.card_of_finrank (ZMod p) (GaloisField p 3) (GaloisField.finrank p (by decide : 3 ≠ 0))]
    simp [Nat.card_zmod, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

private theorem count_submodule (α : GaloisField p 3) (hα : orderOf α = p^3-1)
    (W : Submodule (ZMod p) (GaloisField p 3)) :
    (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) => α^i.val ∈ W).card =
      Nat.card (Projectivization (ZMod p) W) := by
  classical
  let f : {i : Fin (p ^ 2 + p + 1) // α^i.val ∈ W} → Projectivization (ZMod p) W :=
    fun i => Projectivization.mk (ZMod p) (⟨α^i.val.val, i.property⟩ : W)
      (by intro hz; exact pow_ne_zero _ (primitive_ne_zero α hα) (congrArg Subtype.val hz))
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hh := congrArg (Projectivization.map W.subtype W.injective_subtype) hij
      exact Subtype.ext ((projective_bijective α hα).1 hh)
    · intro P
      let P' := Projectivization.map W.subtype W.injective_subtype P
      obtain ⟨i, hi⟩ := (projective_bijective α hα).2 P'
      have hrep : (P.rep : GaloisField p 3) ≠ 0 := by
        intro hz; exact P.rep_nonzero (Subtype.ext hz)
      have he : Projectivization.mk (ZMod p) (α^i.val) (pow_ne_zero _ (primitive_ne_zero α hα)) =
          Projectivization.mk (ZMod p) (P.rep : GaloisField p 3) hrep := by
        change _ = Projectivization.map W.subtype W.injective_subtype (Projectivization.mk (ZMod p) P.rep P.rep_nonzero)
        rw [Projectivization.mk_rep]
        exact hi
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' (ZMod p) _ _ _ _).mp he
      have hmem : α^i.val ∈ W := hc ▸ W.smul_mem c P.rep.property
      refine ⟨⟨i, hmem⟩, ?_⟩
      apply Projectivization.map_injective W.subtype W.injective_subtype
      exact hi
  have he := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at he
  exact he

private theorem singer_card (α : GaloisField p 3) (hα : orderOf α = p^3-1) :
    (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) => Algebra.trace (ZMod p) (GaloisField p 3) (α^i.val) = 0).card = p+1 := by
  have he := count_submodule α hα (Algebra.trace (ZMod p) (GaloisField p 3)).ker
  rw [Projectivization.card_of_finrank_two (ZMod p) _ (kernel_finrank _ (Algebra.trace_surjective _ _)), Nat.card_zmod] at he
  simpa only [LinearMap.mem_ker] using he

private theorem prime_factorization_length : p^3-1 = (p-1)*(p ^ 2 + p + 1) := by
  have hp := (Fact.out : p.Prime).two_le
  have he : p-1+1=p := Nat.sub_add_cancel (by omega)
  have hpow : 1 ≤ p^3 := Nat.one_le_pow 3 p (by omega)
  have he2 := Nat.sub_add_cancel hpow
  nlinarith

private theorem primitive_nonbase_power (α : GaloisField p 3) (hα : orderOf α = p^3-1)
    (r : Fin (p ^ 2 + p + 1)) (hr : r ≠ 0) :
    α^r.val ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)) := by
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact pow_ne_zero _ (primitive_ne_zero α hα) hc.symm
  have hpw : (α^r.val)^(p-1) = 1 := by
    rw [← hc, ← map_pow, ZMod.pow_card_sub_one_eq_one hc0, map_one]
  have hpw' : α ^ (r.val*(p-1)) = 1 := by simpa only [pow_mul] using hpw
  have hd := orderOf_dvd_of_pow_eq_one hpw'
  rw [hα, prime_factorization_length, Nat.mul_comm r.val] at hd
  have hp := (Fact.out : p.Prime).two_le
  have hd' : (p ^ 2 + p + 1) ∣ r.val := (Nat.mul_dvd_mul_iff_left (by omega : 0 < p-1)).mp hd
  have hz : r.val = 0 := Nat.eq_zero_of_dvd_of_lt hd' r.isLt
  exact hr (Fin.ext hz)

private theorem trace_add (α : GaloisField p 3) (hα : α ≠ 0) (i r : Fin (p ^ 2 + p + 1)) :
    Algebra.trace (ZMod p) (GaloisField p 3) (α^(i+r).val) = 0 ↔
      Algebra.trace (ZMod p) (GaloisField p 3) (α^r.val * α^i.val) = 0 := by
  rw [Fin.val_add, ← trace_mod α hα, pow_add, mul_comm]

private theorem singer_difference (α : GaloisField p 3) (hα : orderOf α = p^3-1)
    (r : Fin (p ^ 2 + p + 1)) (hr : r ≠ 0) :
    (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) =>
      Algebra.trace (ZMod p) (GaloisField p 3) (α^i.val) = 0 ∧
      Algebra.trace (ZMod p) (GaloisField p 3) (α^(i+r).val) = 0).card = 1 := by
  let a := α^r.val
  let W := (Algebra.trace (ZMod p) (GaloisField p 3)).ker ⊓
    ((Algebra.trace (ZMod p) (GaloisField p 3)).comp
      (LinearMap.mulLeft (ZMod p) a)).ker
  have he : (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) =>
      Algebra.trace (ZMod p) (GaloisField p 3) (α^i.val) = 0 ∧
      Algebra.trace (ZMod p) (GaloisField p 3) (α^(i+r).val) = 0) =
    (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) => α^i.val ∈ W) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, W, Submodule.mem_inf,
      LinearMap.mem_ker, trace_add α (primitive_ne_zero α hα)]
    rfl
  rw [he, count_submodule α hα, Projectivization.card_of_finrank (ZMod p) W
    (trace_plane_intersection a (primitive_nonbase_power α hα r hr))]
  simp

omit [Fact p.Prime] in
private theorem length_odd : Odd (p ^ 2 + p + 1) := by
  have he : Even (p^2+p) := by
    simpa [pow_two, Nat.mul_add] using Nat.even_mul_succ_self p
  exact he.add_one

private theorem doubleEquiv_val (i : Fin (p ^ 2 + p + 1)) :
    ((show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) i).val = (2*i.val) % (p ^ 2 + p + 1) := by
  have hp := (Fact.out : p.Prime).two_le
  have hn : 2 < (p ^ 2 + p + 1) := by omega
  change ((2 : Fin (p ^ 2 + p + 1)) * i).val = _
  change ((2 % (p ^ 2 + p + 1))*i.val) % (p ^ 2 + p + 1) = _
  rw [Nat.mod_eq_of_lt hn]

private theorem quadric_card (α : GaloisField p 3) (hα : orderOf α = p^3-1) :
    (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) => Algebra.trace (ZMod p) (GaloisField p 3) (α^(2*i.val)) = 0).card = p+1 := by
  rw [← singer_card α hα]
  apply Finset.card_bij (fun i _ => (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [doubleEquiv_val]
    exact (trace_mod α (primitive_ne_zero α hα) _).mp hi
  · intro i _ j _ he
    exact (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).injective he
  · intro j hj
    refine ⟨(show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).symm j, ?_, (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).apply_symm_apply j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    apply (trace_mod α (primitive_ne_zero α hα) _).mpr
    simpa only [← doubleEquiv_val, (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).apply_symm_apply] using hj

private theorem quadric_inverse_doubling (α : GaloisField p 3) (hα : orderOf α = p^3-1) (i : Fin (p ^ 2 + p + 1)) :
    Algebra.trace (ZMod p) (GaloisField p 3) (α^(2*i.val)) = 0 ↔
      Algebra.trace (ZMod p) (GaloisField p 3) (α^((show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) i).val) = 0 := by
  rw [doubleEquiv_val]
  exact trace_mod α (primitive_ne_zero α hα) _

private theorem doubleEquiv_add (i r : Fin (p ^ 2 + p + 1)) :
    (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) (i+r) = (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) i + (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) r := by
  change (2 : Fin (p ^ 2 + p + 1))*(i+r) = 2*i+2*r
  exact mul_add _ _ _

private theorem doubleEquiv_zero : (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) 0 = 0 := by
  change (2 : Fin (p ^ 2 + p + 1))*0 = 0
  simp

private theorem quadric_difference (α : GaloisField p 3) (hα : orderOf α = p^3-1)
    (r : Fin (p ^ 2 + p + 1)) (hr : r ≠ 0) :
    (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) =>
      Algebra.trace (ZMod p) (GaloisField p 3) (α^(2*i.val)) = 0 ∧
      Algebra.trace (ZMod p) (GaloisField p 3) (α^(2*(i+r).val)) = 0).card = 1 := by
  have her : (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) r ≠ 0 := by
    intro hz
    exact hr ((show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).injective (hz.trans doubleEquiv_zero.symm))
  conv_rhs => rw [← singer_difference α hα ((show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) r) her]
  apply Finset.card_bij (fun i _ => (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft) i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [← doubleEquiv_add]
    exact ⟨(quadric_inverse_doubling α hα i).mp hi.1,
      (quadric_inverse_doubling α hα (i+r)).mp hi.2⟩
  · intro i _ j _ he
    exact (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).injective he
  · intro j hj
    refine ⟨(show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).symm j, ?_, (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).apply_symm_apply j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [quadric_inverse_doubling α hα, quadric_inverse_doubling α hα,
      doubleEquiv_add, (show Equiv.Perm (Fin (p ^ 2 + p + 1)) from (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (length_odd (p := p)))).mulLeft).apply_symm_apply]
    exact hj


/-- Singer's cubic difference set and the inverse image under index doubling. -/
theorem result (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1) :
    (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) =>
      Algebra.trace (ZMod p) (GaloisField p 3) (α ^ i.val) = 0).card = p + 1 ∧
    (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) =>
      Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (2 * i.val)) = 0).card = p + 1 ∧
    (∀ r : Fin (p ^ 2 + p + 1), r ≠ 0 →
      (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) =>
        Algebra.trace (ZMod p) (GaloisField p 3) (α ^ i.val) = 0 ∧
        Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (i + r).val) = 0).card = 1) ∧
    (∀ i : Fin (p ^ 2 + p + 1),
      Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (2 * i.val)) = 0 ↔
      Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (2 * i).val) = 0) ∧
    (∀ r : Fin (p ^ 2 + p + 1), r ≠ 0 →
      (Finset.univ.filter fun i : Fin (p ^ 2 + p + 1) =>
        Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (2 * i.val)) = 0 ∧
        Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (2 * (i + r).val)) = 0).card = 1) := by
  exact ⟨singer_card α hα, quadric_card α hα, singer_difference α hα,
    quadric_inverse_doubling α hα, quadric_difference α hα⟩

end D5.S3.Geometry.FiniteGeometry.SingerTracePlane
