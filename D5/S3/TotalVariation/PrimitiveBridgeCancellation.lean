/- GID: D5/S3/TotalVariation/PrimitiveBridgeCancellation
   generality: G
   mirror-B: D5/B/S3/TotalVariation/PrimitiveBridgeCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive stochastic bridges give integer lattice generators and phase cancellation. -/

import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic

open scoped BigOperators
open Quiver Quiver.Path
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.TotalVariation.PrimitiveBridgeCancellation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual supported paths with prescribed length and endpoints, including length zero. -/
abbrev Gamma (P : Matrix V V ℝ) (n : ℕ) (i j : V) :=
  letI : Quiver V := Matrix.toQuiver P
  {p : Quiver.Path i j // p.length = n}

/-- All equal-length, equal-endpoint integer charge differences over every supported path. -/
def differences (P : Matrix V V ℝ) {q : ℕ} (g : V → V → (Fin q → ℤ)) :
    Set (Fin q → ℤ) :=
  letI : Quiver V := Matrix.toQuiver P
  {lam | ∃ (n : ℕ) (i j : V) (a b : Gamma P n i j),
    lam = a.val.addWeightOfEPs g - b.val.addWeightOfEPs g}

/-- The integer span of the original supported path differences. -/
def lattice (P : Matrix V V ℝ) {q : ℕ} (g : V → V → (Fin q → ℤ)) :=
  Submodule.span ℤ (differences P g)

/-- The real pairing used in the charge characters. -/
def dot {q : ℕ} (x : Fin q → ℝ) (lam : Fin q → ℤ) : ℝ :=
  ∑ k, x k * (lam k : ℝ)

/-- The actual transition matrix with its edge-charge phases. -/
def twisted (P : Matrix V V ℝ) {q : ℕ} (g : V → V → (Fin q → ℤ))
    (x : Fin q → ℝ) : Matrix V V ℂ :=
  fun i j => (P i j : ℂ) * Complex.exp ((dot x (g i j) : ℂ) * Complex.I)

/-- The full periodic inverse image of the integer path-lattice annihilator. -/
def annihilator (P : Matrix V V ℝ) {q : ℕ} (g : V → V → (Fin q → ℤ)) :
    Set (Fin q → ℝ) :=
  {x | ∀ lam ∈ lattice P g, ∃ z : ℤ, dot x lam = (2 * Real.pi) * z}

/-- The finite cosine deficit associated with a set of distinct charge vectors. -/
noncomputable def energy {q : ℕ} (F : Finset (Fin q → ℤ)) (x : Fin q → ℝ) : ℝ :=
  ∑ lam ∈ F, (1 - Real.cos (dot x lam))

/-- A primitive stochastic matrix admits one common positive-length bridge carrying
an integer generating set of all original path differences. Actual positive path
weights bound a uniform scalar-entry cancellation deficit, and its finite cosine
zero set is exactly the full original lattice annihilator. -/
theorem primitive_bridge_cancellation [Nonempty V]
    (P : Matrix V V ℝ) (hstoch : P ∈ Matrix.rowStochastic ℝ V)
    (hprim : Matrix.IsPrimitive P) {q : ℕ} (g : V → V → (Fin q → ℤ))
    (iStar jStar : V) :
    letI : Quiver V := Matrix.toQuiver P
    ∃ L : ℕ, 0 < L ∧ ∃ F : Finset (Fin q → ℤ), ∃ c : ℝ, 0 < c ∧
      Submodule.span ℤ (F : Set (Fin q → ℤ)) = lattice P g ∧
      (∀ lam ∈ F, ∃ a b : Gamma P L iStar jStar,
        a.val.addWeightOfEPs g - b.val.addWeightOfEPs g = lam ∧
        c ≤ a.val.weightOfEPs (fun i j => P i j) * b.val.weightOfEPs (fun i j => P i j)) ∧
      0 < (P ^ L) iStar jStar ∧
      (∀ x : Fin q → ℝ, c * energy F x ≤
        ((P ^ L) iStar jStar)^2 - ‖(twisted P g x ^ L) iStar jStar‖^2) ∧
      (∀ x : Fin q → ℝ, energy F x = 0 ↔ x ∈ annihilator P g) := by
  classical
  have hP := hprim.nonneg
  let : Quiver V := Matrix.toQuiver P
  let : ∀ a b : V, Subsingleton (a ⟶ b) := fun _ _ => inferInstanceAs (Subsingleton (PLift _))
  have hlen {i j : V} (p : Path i j) : p.toList.length = p.length := by
    induction p with
    | nil => rfl
    | cons p e ih => simpa using congrArg Nat.succ ih
  have hfinite (n : ℕ) (i j : V) : Finite (Gamma P n i j) := by
    let f : Gamma P n i j → List.Vector V n := fun p => ⟨p.val.toList, by rw [hlen, p.property]⟩
    apply Finite.of_injective f
    intro a b h
    apply Subtype.ext
    exact Quiver.Path.toList_injective i j (congrArg (fun l : List.Vector V n => l.val) h)
  let inst : ∀ n i j, Fintype (Gamma P n i j) := fun n i j => @Fintype.ofFinite _ (hfinite n i j)
  let hstep (n : ℕ) (i j : V) :
      (Σ k : V, Gamma P n i k × PLift (0 < P k j)) ≃ Gamma P (n + 1) i j := by
    let f : (Σ k : V, Gamma P n i k × PLift (0 < P k j)) → Gamma P (n + 1) i j :=
      fun s => ⟨s.2.1.val.cons s.2.2, by simp [s.2.1.property]⟩
    apply Equiv.ofBijective f
    constructor
    · rintro ⟨k, a, e⟩ ⟨l, b, d⟩ h
      have hh := Quiver.Path.cons.inj (congrArg Subtype.val h)
      obtain rfl := hh.1
      have hab : a = b := Subtype.ext (eq_of_heq hh.2.1)
      subst b
      have hed : e = d := Subsingleton.elim _ _
      subst d
      rfl
    · rintro ⟨p, hp⟩
      cases p with
      | nil => simp at hp
      | @cons k _ p e =>
        exact ⟨⟨k, ⟨p, Nat.succ.inj hp⟩, e⟩, rfl⟩
  have hexpand (A : Matrix V V ℂ) (hA : ∀ i j, ¬ 0 < P i j → A i j = 0)
      (n : ℕ) (i j : V) :
      (A ^ n) i j = ∑ p : Gamma P n i j, p.val.weightOfEPs (fun i j => A i j) := by
    induction n generalizing i j with
    | zero =>
      by_cases hij : i = j
      · subst j
        let z : Gamma P 0 i i := ⟨Path.nil, rfl⟩
        have hz (p : Gamma P 0 i i) : p = z :=
          Subtype.ext (Quiver.Path.eq_nil_of_length_zero _ p.property)
        let : Unique (Gamma P 0 i i) := ⟨⟨z⟩, hz⟩
        rw [Fintype.sum_unique, hz default]
        simp [z, Quiver.Path.weightOfEPs_nil]
      · have : IsEmpty (Gamma P 0 i j) := ⟨fun p => hij (p.val.eq_of_length_zero p.property)⟩
        simp [hij]
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply, ← (hstep n i j).sum_comp]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih]
      by_cases hk : 0 < P k j
      · let : Unique (PLift (0 < P k j)) := ⟨⟨⟨hk⟩⟩, fun _ => Subsingleton.elim _ _⟩
        simp only [Fintype.sum_prod_type, Fintype.sum_unique, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        dsimp only [hstep]
        rw [Equiv.ofBijective_apply]
        exact (Quiver.Path.weightOfEPs_cons (fun i j => A i j) p.val
          (default : PLift (0 < P k j))).symm
      · have : IsEmpty (PLift (0 < P k j)) := ⟨fun e => hk e.down⟩
        simp [hA k j hk]
  have hweight (x : Fin q → ℝ) {i j : V} (p : Path i j) :
      p.weightOfEPs (fun i j => twisted P g x i j) = ((p.weightOfEPs (fun i j => P i j) : ℝ) : ℂ) *
        Complex.exp ((dot x (p.addWeightOfEPs g) : ℂ) * Complex.I) := by
    induction p with
    | nil => simp [Quiver.Path.weightOfEPs_nil, Quiver.Path.addWeightOfEPs_nil, dot]
    | @cons k l p e ih =>
      rw [Quiver.Path.weightOfEPs_cons, Quiver.Path.weightOfEPs_cons,
        Quiver.Path.addWeightOfEPs_cons, ih]
      have hd : dot x (p.addWeightOfEPs g + g k l) =
          dot x (p.addWeightOfEPs g) + dot x (g k l) := by
        simp [dot, mul_add, Finset.sum_add_distrib]
      rw [hd]
      simp only [Complex.ofReal_add, Complex.ofReal_mul, add_mul, Complex.exp_add, twisted]
      ring
  have hreal (n : ℕ) (i j : V) : (P ^ n) i j =
      ∑ p : Gamma P n i j, p.val.weightOfEPs (fun i j => P i j) := by
    have he := hexpand (P.map Complex.ofRealHom) (by
      intro i j hp
      simp [le_antisymm (le_of_not_gt hp) (hP i j)]) n i j
    rw [← Matrix.map_pow] at he
    have hw {i j : V} (p : Path i j) :
        p.weightOfEPs (fun i j => (P i j : ℂ)) = ((p.weightOfEPs (fun i j => P i j) : ℝ) : ℂ) := by
      induction p with
      | nil => simp [Quiver.Path.weightOfEPs_nil]
      | cons p e ih => simp [Quiver.Path.weightOfEPs_cons, ih]
    simpa [hw] using congrArg Complex.re he
  have htwist (x : Fin q → ℝ) (n : ℕ) (i j : V) :
      (twisted P g x ^ n) i j = ∑ p : Gamma P n i j,
        ((p.val.weightOfEPs (fun i j => P i j) : ℝ) : ℂ) *
          Complex.exp ((dot x (p.val.addWeightOfEPs g) : ℂ) * Complex.I) := by
    rw [hexpand (twisted P g x) (by
      intro i j hp
      have hz : P i j = 0 := le_antisymm (le_of_not_gt hp) (hP i j)
      simp [twisted, hz])]
    exact Finset.sum_congr rfl (fun p _ => hweight x p.val)

  obtain ⟨N, hN0, hN⟩ := hprim.exists_pos_pow
  have htail (r : ℕ) (i j : V) : 0 < (P ^ (r + N)) i j := by
    have hr := (Matrix.rowStochastic ℝ V).pow_mem hstoch r
    have hn (k : V) : 0 ≤ (P ^ r) i k := hr.1 i k
    have hs : 0 < ∑ k, (P ^ r) i k := by
      rw [Matrix.sum_row_of_mem_rowStochastic hr]
      exact zero_lt_one
    obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ => hn k)).mp hs
    rw [pow_add, Matrix.mul_apply]
    exact (mul_pos hk (hN k j)).trans_le
      (Finset.single_le_sum (fun l _ => mul_nonneg (hn l) (hN l j).le) (Finset.mem_univ k))
  obtain ⟨F0, hF0, hspan0⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (R := ℤ) (differences P g)).mp (IsNoetherian.noetherian (lattice P g))
  let F := F0.erase 0
  have hFD : (F : Set (Fin q → ℤ)) ⊆ differences P g :=
    fun _ h => hF0 (Finset.mem_of_mem_erase h)
  have hspan : Submodule.span ℤ (differences P g) = Submodule.span ℤ (F : Set (Fin q → ℤ)) := by
    rw [hspan0]
    simpa [F] using
      (Submodule.span_sdiff_singleton_zero (R := ℤ) (s := (F0 : Set (Fin q → ℤ)))).symm
  have hselected (lam : F) : ∃ (n : ℕ) (i j : V) (a b : Gamma P n i j),
      lam.val = a.val.addWeightOfEPs g - b.val.addWeightOfEPs g := hFD lam.property
  choose n u v a b hd using hselected
  let R := Finset.univ.sup n
  have hn (lam : F) : n lam ≤ R := Finset.le_sup (Finset.mem_univ lam)
  let L := N + R + N
  have hL : 0 < L := by dsimp [L]; omega
  let pre (lam : F) : Gamma P N iStar (u lam) := Classical.choice
    ((Matrix.pow_apply_pos_iff_nonempty_path hprim.nonneg N iStar (u lam)).mp (hN _ _))
  let post (lam : F) : Gamma P (R - n lam + N) (v lam) jStar := Classical.choice
    ((Matrix.pow_apply_pos_iff_nonempty_path hprim.nonneg (R - n lam + N) (v lam) jStar).mp
      (htail (R - n lam) _ _))
  let aa (lam : F) : Gamma P L iStar jStar :=
    ⟨(pre lam).val.comp ((a lam).val.comp (post lam).val), by
      simp only [Quiver.Path.length_comp, (pre lam).property, (a lam).property,
        (post lam).property]
      dsimp [L]
      have := hn lam
      omega⟩
  let bb (lam : F) : Gamma P L iStar jStar :=
    ⟨(pre lam).val.comp ((b lam).val.comp (post lam).val), by
      simp only [Quiver.Path.length_comp, (pre lam).property, (b lam).property,
        (post lam).property]
      dsimp [L]
      have := hn lam
      omega⟩
  have hdiff (lam : F) : (aa lam).val.addWeightOfEPs g -
      (bb lam).val.addWeightOfEPs g = lam.val := by
    dsimp [aa, bb]
    simp only [Quiver.Path.addWeightOfEPs_comp]
    rw [hd lam]
    abel
  let w (p : Gamma P L iStar jStar) : ℝ := p.val.weightOfEPs (fun i j => P i j)
  have hw (p : Gamma P L iStar jStar) : 0 < w p := by
    apply Quiver.Path.weight_pos
    intro i j e
    exact e.down
  let T : Finset ℝ := insert 1 (Finset.univ.image (fun lam : F => w (aa lam) * w (bb lam)))
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let c : ℝ := T.min' hT
  have hc : 0 < c := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact zero_lt_one
    · obtain ⟨lam, _, rfl⟩ := Finset.mem_image.mp ht
      exact mul_pos (hw _) (hw _)
  have hcb (lam : F) : c ≤ w (aa lam) * w (bb lam) :=
    Finset.min'_le T _ (by simp [T])
  have hinj : Function.Injective (fun lam : F => (aa lam, bb lam)) := by
    intro lam mu h
    apply Subtype.ext
    rw [← hdiff lam, ← hdiff mu]
    have ha : aa lam = aa mu := congrArg Prod.fst h
    have hb : bb lam = bb mu := congrArg Prod.snd h
    rw [ha, hb]
  have hzero (x : Fin q → ℝ) : energy F x = 0 ↔ x ∈ annihilator P g := by
    have hf : energy F x = 0 ↔ ∀ lam ∈ F, ∃ z : ℤ, dot x lam = (2 * Real.pi) * z := by
      rw [energy, Finset.sum_eq_zero_iff_of_nonneg
        (fun lam _ => sub_nonneg.mpr (Real.cos_le_one _))]
      apply forall₂_congr
      intro lam _
      rw [sub_eq_zero, eq_comm, Real.cos_eq_one_iff]
      simp only [mul_comm, eq_comm]
    let K : Submodule ℤ (Fin q → ℤ) := {
      carrier := {lam | ∃ z : ℤ, dot x lam = (2 * Real.pi) * z}
      zero_mem' := ⟨0, by simp [dot]⟩
      add_mem' := by
        rintro lam mu ⟨z, hz⟩ ⟨t, ht⟩
        refine ⟨z + t, ?_⟩
        have hd : dot x (lam + mu) = dot x lam + dot x mu := by
          simp [dot, mul_add, Finset.sum_add_distrib]
        rw [hd, hz, ht, Int.cast_add, mul_add]
      smul_mem' := by
        rintro z lam ⟨t, ht⟩
        refine ⟨z * t, ?_⟩
        have hd : dot x (z • lam) = (z : ℝ) * dot x lam := by
          simp [dot, Finset.mul_sum, mul_left_comm]
        rw [hd, ht, Int.cast_mul]
        ring }
    rw [hf]
    constructor
    · intro h lam hlam
      have hh : Submodule.span ℤ (F : Set (Fin q → ℤ)) ≤ K := Submodule.span_le.mpr h
      exact hh (hspan ▸ hlam)
    · intro h lam hlam
      apply h
      rw [lattice, hspan]
      exact Submodule.subset_span hlam
  refine ⟨L, hL, F, c, hc, hspan.symm, ?_, ?_, ?_, hzero⟩
  · intro lam hlam
    exact ⟨aa ⟨lam, hlam⟩, bb ⟨lam, hlam⟩, hdiff ⟨lam, hlam⟩, hcb ⟨lam, hlam⟩⟩
  · exact htail (N + R) iStar jStar
  · intro x
    let t (p : Gamma P L iStar jStar) : ℝ := dot x (p.val.addWeightOfEPs g)
    let d (p r : Gamma P L iStar jStar) : ℝ :=
      w p * w r * (1 - Real.cos (t p - t r))
    have hdnonneg (p r : Gamma P L iStar jStar) : 0 ≤ d p r :=
      mul_nonneg (mul_nonneg (hw p).le (hw r).le) (sub_nonneg.mpr (Real.cos_le_one _))
    have hdot (p r : Gamma P L iStar jStar) :
        t p - t r = dot x (p.val.addWeightOfEPs g - r.val.addWeightOfEPs g) := by
      simp [t, dot, mul_sub, Finset.sum_sub_distrib]
    have hpair : (∑ p : Gamma P L iStar jStar, ∑ r : Gamma P L iStar jStar, d p r) =
        (P ^ L) iStar jStar ^ 2 - ‖(twisted P g x ^ L) iStar jStar‖ ^ 2 := by
      rw [hreal, htwist, ← Complex.normSq_eq_norm_sq]
      change (∑ p, ∑ r, d p r) = (∑ p, w p)^2 -
        Complex.normSq (∑ p, (w p : ℂ) * Complex.exp ((t p : ℂ) * Complex.I))
      calc
        _ = ∑ p, ∑ r, (w p * w r - (w p * Real.cos (t p)) * (w r * Real.cos (t r)) -
            (w p * Real.sin (t p)) * (w r * Real.sin (t r))) := by
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro r _
          dsimp [d]
          rw [Real.cos_sub]
          ring
        _ = _ := by
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
          simp [Complex.normSq_apply,
            Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
            Complex.exp_ofReal_mul_I_im]
          ring
    rw [← hpair]
    let f : F → Gamma P L iStar jStar × Gamma P L iStar jStar := fun lam => (aa lam, bb lam)
    calc
      c * energy F x = ∑ lam : F, c * (1 - Real.cos (dot x lam.val)) := by
        rw [energy, Finset.mul_sum, Finset.sum_subtype F (fun _ => Iff.rfl)]
      _ ≤ ∑ lam : F, d (aa lam) (bb lam) := by
        apply Finset.sum_le_sum
        intro lam _
        dsimp [d]
        rw [hdot, hdiff]
        exact mul_le_mul_of_nonneg_right (hcb lam) (sub_nonneg.mpr (Real.cos_le_one _))
      _ = ∑ pr ∈ Finset.univ.image f, d pr.1 pr.2 := by
        rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      _ ≤ ∑ pr : Gamma P L iStar jStar × Gamma P L iStar jStar, d pr.1 pr.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro pr _ _
        exact hdnonneg _ _
      _ = _ := Fintype.sum_prod_type _

end D5.S3.TotalVariation.PrimitiveBridgeCancellation
