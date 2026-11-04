/- GID: D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourZhuFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite dimension of the literal actual norm-four Zhu additive quotient. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Exact
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourZhuFinite

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeActualStateFieldCalculus
open NormFourVirasoroVector NormFourVacuumIrreducible NormFourVacuumC2
open scoped BigOperators VertexOperator

open private word wordGrade word_mem word_eigen gradeSpace grade_eigen
  assemble components_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
open private full_field_closed coefficient_grading
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
open private representatives representatives_mem small small_le three_spanning
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2
open private pair pairGrade pairSpace pair_space_eigen c2_decompose
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Exact

noncomputable section

/-- Actual homogeneous Zhu circle product, including its entire finite sum. -/
def circle (D : LatticeData) (n : ℕ) (u v : Carrier D) : Carrier D :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) • mu D u ((j:ℤ)-2) v

/-- Both states lie in the same actual vacuum algebra. The weight condition
uses its actual axis L0, without an assumed abstract grading. -/
def zhuO (D : LatticeData) (a : Charge D) (s : ℂ) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ {z | ∃ (n : ℕ) (u v : Carrier D),
    u ∈ vacuumDescendants D a s ∧ v ∈ vacuumDescendants D a s ∧
    mode D a s 0 u = (n:ℂ) • u ∧ z = circle D n u v}

private theorem circle_mem (D : LatticeData) (a : Charge D) (s : ℂ)
    (n : ℕ) (u v : Carrier D) (hu : u ∈ vacuumDescendants D a s)
    (hv : v ∈ vacuumDescendants D a s)
    (he : mode D a s 0 u = (n:ℂ) • u) : circle D n u v ∈ zhuO D a s :=
  Submodule.subset_span ⟨n,u,v,hu,hv,he,rfl⟩

private theorem zhuO_le (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    zhuO D a s ≤ vacuumDescendants D a s := by
  apply Submodule.span_le.mpr
  rintro z ⟨n,u,v,hu,hv,_,rfl⟩
  apply Submodule.sum_mem
  intro j _
  exact (vacuumDescendants D a s).smul_mem _
    (full_field_closed D a ha s hs u hu _ v hv)

private theorem grade_le_actual (D : LatticeData) (a : Charge D) (s : ℂ)
    (n : ℕ) : gradeSpace D a s n ≤ vacuumDescendants D a s := by
  apply Submodule.span_le.mpr
  rintro v ⟨w,_,rfl⟩
  exact word_mem D a s w

private theorem representative_eigen (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (i : Fin 3) :
    mode D a s 0 (representatives D a s i) =
      (2*i.val:ℂ) • representatives D a s i := by
  fin_cases i
  · simpa [representatives,word,wordGrade] using word_eigen D a ha s hs []
  · simpa [representatives,word,wordGrade] using word_eigen D a ha s hs [1]
  · convert word_eigen D a ha s hs [1,1] using 1 <;>
      norm_num [representatives,word,wordGrade,pow_succ',Module.End.mul_apply]

-- The existing three representatives have a finite homogeneous expansion.
-- This neither assumes their independence nor adds a homogeneous O-space.
private theorem small_decompose (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (z : Carrier D) (hz : z ∈ small D a s) :
    ∃ f : ℕ →₀ Carrier D, assemble D f = z ∧
      (∀ n, f n ∈ small D a s) ∧
      ∀ n, mode D a s 0 (f n) = (n:ℂ) • f n := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i,rfl⟩ := hz
      refine ⟨Finsupp.single (2*i.val) (representatives D a s i), ?_, ?_, ?_⟩
      · simp [assemble,Finsupp.lsum_single]
      · intro n
        by_cases hn : 2*i.val=n
        · subst n
          rw [Finsupp.single_eq_same]
          change representatives D a s i ∈ Submodule.span ℂ (Set.range (representatives D a s))
          exact Submodule.subset_span ⟨i,rfl⟩
        · simp [hn]
      · intro n
        by_cases hn : 2*i.val=n
        · subst n
          simpa only [Finsupp.single_eq_same,Nat.cast_mul,Nat.cast_ofNat] using
            representative_eigen D a ha s hs i
        · simp [hn]
  | zero => exact ⟨0,by simp,by simp,by simp⟩
  | add u v _ _ hu hv =>
      obtain ⟨f,hf,hfm,hfe⟩ := hu
      obtain ⟨g,hg,hgm,hge⟩ := hv
      exact ⟨f+g,by rw [map_add,hf,hg],
        fun n => (small D a s).add_mem (hfm n) (hgm n),
        fun n => by simp only [Finsupp.add_apply,map_add,hfe,hge,smul_add]⟩
  | smul c u _ hu =>
      obtain ⟨f,hf,hfm,hfe⟩ := hu
      refine ⟨c • f,by rw [map_smul,hf],
        fun n => (small D a s).smul_mem c (hfm n),?_⟩
      intro n
      simp only [Finsupp.smul_apply,map_smul,hfe,smul_smul,mul_comm]

-- Extract the N-component from the accepted C2 + three-vector spanning
-- identity. Polynomial projectors are used only in the zero subspace;
-- no invariance or gradedness of Zhu O is asserted or used.
private theorem homogeneous_spanning (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (v : Carrier D) (hv : v ∈ vacuumDescendants D a s)
    (he : mode D a s 0 v = (n:ℂ) • v) :
    v ∈ pairSpace D a s n ⊔ small D a s := by
  obtain ⟨z,hz,t,ht,eq⟩ := Submodule.mem_sup.mp
    (three_spanning D a ha s hs hv)
  obtain ⟨f,hf,hfg⟩ := c2_decompose D a s z hz
  obtain ⟨g,hg,hgm,hge⟩ := small_decompose D a ha s hs t ht
  let h : ℕ →₀ Carrier D := f+g-Finsupp.single n v
  have eigen (j : ℕ) : mode D a s 0 (h j) = (j:ℂ) • h j := by
    by_cases hj : j=n
    · subst j
      simp only [h,Finsupp.sub_apply,Finsupp.add_apply,Finsupp.single_eq_same,
        map_sub,map_add,pair_space_eigen D a ha s hs n _ (hfg n),hge,he,
        smul_add,smul_sub]
    · simpa only [h,Finsupp.sub_apply,Finsupp.add_apply,
        Finsupp.single_eq_of_ne hj,sub_zero,map_add,smul_add] using
        congrArg₂ (fun x y : Carrier D => x+y)
          (pair_space_eigen D a ha s hs j _ (hfg j)) (hge j)
  have zero : assemble D h ∈ (⊥ : Submodule ℂ (Carrier D)) := by
    change assemble D h = 0
    simp only [h,map_sub,map_add,hf,hg]
    simp only [assemble,Finsupp.lsum_single,LinearMap.id_apply,eq,sub_self]
  have component := components_mem D a s h eigen ⊥
    (by intro u hu; have h0 : u=0 := hu; subst u; simp) zero n
  have eqn : f n+g n=v := sub_eq_zero.mp (by simpa [h] using component)
  exact Submodule.mem_sup.mpr ⟨f n,hfg n,g n,hgm n,eqn⟩

-- A literal C2 pair of grade N equals a Zhu circle minus terms of
-- STRICTLY SMALLER actual grade. Every term of the circle sum is retained.
private theorem pair_space_step (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (n : ℕ)
    (ih : ∀ j<n, gradeSpace D a s j ≤ zhuO D a s ⊔ small D a s) :
    pairSpace D a s n ≤ zhuO D a s ⊔ small D a s := by
  classical
  apply Submodule.span_le.mpr
  rintro z ⟨p,hp,rfl⟩
  let α := wordGrade p.1
  let β := wordGrade p.2
  let u := word D a s p.1
  let v := word D a s p.2
  let S := vacuumDescendants D a s
  let uS : S := ⟨u,word_mem D a s p.1⟩
  let vS : S := ⟨v,word_mem D a s p.2⟩
  have hu : uS ∈ NormFourVacuumVertexAlgebra.grade D a s α :=
    Submodule.subset_span ⟨p.1,rfl,rfl⟩
  have hv : vS ∈ NormFourVacuumVertexAlgebra.grade D a s β :=
    Submodule.subset_span ⟨p.2,rfl,rfl⟩
  have grade_eq : α+β+1=n := hp
  let correction : Carrier D :=
    ∑ j ∈ Finset.range α, (α.choose (j+1):ℂ) • mu D u ((j:ℤ)-1) v
  have hc : circle D α u v = pair D a s p+correction := by
    unfold circle
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right,Nat.cast_one,one_smul,Nat.cast_zero,
      zero_sub]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    push_cast
    ring
  have circle_in : circle D α u v ∈ zhuO D a s ⊔ small D a s := by
    exact Submodule.mem_sup_left (circle_mem D a s α u v
      (word_mem D a s p.1) (word_mem D a s p.2)
      (word_eigen D a ha s hs p.1))
  have correction_in : correction ∈ zhuO D a s ⊔ small D a s := by
    apply Submodule.sum_mem
    intro j hj
    apply (zhuO D a s ⊔ small D a s).smul_mem
    have hjα : j<α := Finset.mem_range.mp hj
    have nonneg : 0 ≤ (α:ℤ)+(β:ℤ)-((j:ℤ)-1)-1 := by omega
    have hgrade := (coefficient_grading D a ha s hs α β ((j:ℤ)-1)
      uS vS hu hv).1 nonneg
    have idx : ((α:ℤ)+(β:ℤ)-((j:ℤ)-1)-1).toNat = n-(j+1) := by omega
    rw [idx] at hgrade
    change mu D u ((j:ℤ)-1) v ∈ gradeSpace D a s (n-(j+1)) at hgrade
    exact ih (n-(j+1)) (by omega) hgrade
  have result := (zhuO D a s ⊔ small D a s).sub_mem circle_in correction_in
  change pair D a s p ∈ zhuO D a s ⊔ small D a s
  simpa only [hc,add_sub_cancel_right] using result

private theorem zhu_three_spanning (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s ≤ zhuO D a s ⊔ small D a s := by
  have every_grade : ∀ n, gradeSpace D a s n ≤ zhuO D a s ⊔ small D a s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro v hv
        obtain ⟨p,hp,t,ht,eq⟩ := Submodule.mem_sup.mp
          (homogeneous_spanning D a ha s hs n v (grade_le_actual D a s n hv)
            (grade_eigen D a ha s hs n v hv))
        rw [← eq]
        exact (zhuO D a s ⊔ small D a s).add_mem
          (pair_space_step D a ha s hs n ih hp) (Submodule.mem_sup_right ht)
  apply Submodule.span_le.mpr
  rintro v ⟨w,rfl⟩
  exact every_grade (wordGrade w) (Submodule.subset_span ⟨w,rfl,rfl⟩)

/-- Finiteness and a concrete upper bound for the literal actual Zhu
O-space quotient. This supplies no quotient multiplication and no exact
dimension, rationality, fusion rule or conformal-field classification. -/
theorem actual_zhu_quotient_finite (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := vacuumDescendants D a s
    let O := (zhuO D a s).comap S.subtype
    zhuO D a s ≤ S ∧
      FiniteDimensional ℂ (S ⧸ O) ∧ Module.finrank ℂ (S ⧸ O) ≤ 3 := by
  classical
  let S := vacuumDescendants D a s
  let O := (zhuO D a s).comap S.subtype
  let Q := S ⧸ O
  let q : S →ₗ[ℂ] Q := O.mkQ
  have ole := zhuO_le D a ha s hs
  have sle := small_le D a ha s hs
  let r : Fin 3 → S := fun i =>
    ⟨representatives D a s i,representatives_mem D a ha s hs i⟩
  let R : Submodule ℂ Q := Submodule.span ℂ (Set.range fun i => q (r i))
  have small_image_aux : small D a s ≤ (R.comap q).map S.subtype := by
    apply Submodule.span_le.mpr
    rintro z ⟨i,rfl⟩
    exact Submodule.mem_map.mpr ⟨r i,Submodule.subset_span ⟨i,rfl⟩,rfl⟩
  have small_image (z : Carrier D) (hz : z ∈ small D a s) : q ⟨z,sle hz⟩ ∈ R := by
    obtain ⟨w,hw,he⟩ := Submodule.mem_map.mp (small_image_aux hz)
    have equal : w=⟨z,sle hz⟩ := Subtype.ext he
    exact equal ▸ hw
  have span_top : R=⊤ := by
    apply top_unique
    intro x _
    obtain ⟨v,rfl⟩ := O.mkQ_surjective x
    obtain ⟨u,hu,z,hz,eq⟩ := Submodule.mem_sup.mp
      (zhu_three_spanning D a ha s hs v.property)
    have hzero : q ⟨u,ole hu⟩=0 := (Submodule.Quotient.mk_eq_zero O).mpr hu
    have split : (⟨u,ole hu⟩:S)+⟨z,sle hz⟩=v := Subtype.ext eq
    rw [← split,map_add,hzero,zero_add]
    exact small_image z hz
  have finite : FiniteDimensional ℂ Q := Module.Finite.of_fg_top (by
    rw [← span_top]
    exact Submodule.fg_span (Set.finite_range _))
  have bound : Module.finrank ℂ Q ≤ 3 := by
    simpa using finrank_le_of_span_eq_top span_top
  exact ⟨ole,finite,bound⟩

end
end D5.S3.VertexAlgebra.Lattice.NormFourZhuFinite
