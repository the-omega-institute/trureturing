/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive
   generality: I
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=none
   digest: A complex evolution algebra contains a three-dimensional minimal idempotent subspace. -/

/-
proof_shape: result: content
admission_basis: open-problem-resolution (issue #12879)
Direct frozen dependencies: none (pinned Mathlib only).
The live structural argument classifies all subalgebras of the embedded space,
using a square-zero plane and generation from a nonzero first coordinate.
The question is Barei's Remark 3.5, with Muse Spark. The realization is in the
spirit of the evolution-envelope framework of Costoya--Fernandez Ouaridi--Viruel.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.BareiRemarkThreeFive

private abbrev A := Fin 3 → ℂ

abbrev E := Fin 5 → ℂ

private def mul (x y : A) : A :=
  ![4*x 0*y 0,
    2*x 0*y 1+2*x 1*y 0+2*x 0*y 2+2*x 2*y 0,
    2*x 0*y 0+2*x 0*y 2+2*x 2*y 0]

private def u : A := ![1,0,0]

private def v : A := ![0,1,0]

private def w : A := ![0,0,1]

private def square (U : Submodule ℂ (A)) : Submodule ℂ (A) :=
  Submodule.span ℂ {z | ∃ x ∈ U, ∃ y ∈ U, mul x y = z}

private def embed : A →ₗ[ℂ] E where
  toFun x := ![x 0,x 0+x 1,x 0-x 1,x 0+x 2,x 0-x 2]
  map_add' x y := by ext i; fin_cases i <;> dsimp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> dsimp <;> ring

private def ambientMul (x y : E) : E :=
  ![4*x 0*y 0,
    4*x 0*y 0+x 1*y 1-x 2*y 2+x 3*y 3-x 4*y 4,
    4*x 0*y 0-x 1*y 1+x 2*y 2-x 3*y 3+x 4*y 4,
    6*x 0*y 0+x 3*y 3-x 4*y 4,
    2*x 0*y 0-x 3*y 3+x 4*y 4]

private def ambientSquare (U : Submodule ℂ (E)) : Submodule ℂ (E) :=
  Submodule.span ℂ {z | ∃ x ∈ U, ∃ y ∈ U, ambientMul x y = z}

private def V : Submodule ℂ (E) := (embed).range

/-- Span of all pair products in a complex linear subspace. -/
def Square (μ : E →ₗ[ℂ] E →ₗ[ℂ] E) (U : Submodule ℂ E) : Submodule ℂ E :=
  Submodule.span ℂ {z | ∃ x ∈ U, ∃ y ∈ U, μ x y = z}

/-- Affirmative answer to Barei's Remark 3.5, with an explicit five-dimensional ambient space. -/
theorem result :    ∃ μ : E →ₗ[ℂ] E →ₗ[ℂ] E, ∃ b : Module.Basis (Fin 5) ℂ E,
      ∃ V : Submodule ℂ E,
        Module.finrank ℂ E = 5 ∧
        (∀ i j : Fin 5, i ≠ j → μ (b i) (b j) = 0) ∧
        Module.finrank ℂ V = 3 ∧ Square μ V = V ∧
        ∀ U : Submodule ℂ E,
          U ≤ V → U ≠ ⊥ → Square μ U = U → U = V := by
  classical
  have product_mem_square {U : Submodule ℂ (A)} {x y : A}
      (hx : x ∈ U) (hy : y ∈ U) : mul x y ∈ square U :=
    Submodule.subset_span ⟨x,hx,y,hy,rfl⟩
  have top_of_basis_mem (U : Submodule ℂ (A))
      (hu : u ∈ U) (hv : v ∈ U) (hw : w ∈ U) : U = ⊤ := by
    apply top_unique
    intro y _
    have he : y = y 0 • u + y 1 • v + y 2 • w := by
      ext i; fin_cases i <;> dsimp [u,v,w] <;> ring
    rw [he]
    exact U.add_mem (U.add_mem (U.smul_mem _ hu) (U.smul_mem _ hv)) (U.smul_mem _ hw)
  have generates (U : Submodule ℂ (A))
      (closed : ∀ x ∈ U, ∀ y ∈ U, mul x y ∈ U)
      (x : A) (hx : x ∈ U) (ha : x 0 ≠ 0) : U = ⊤ := by
    let s := mul x x - (4*x 0) • x
    have hs : s ∈ U := U.sub_mem (closed x hx x hx) (U.smul_mem _ hx)
    have ht : mul x s - (2*x 0) • s = (4*x 0^3) • v := by
      ext i; fin_cases i <;> dsimp [s,mul,v] <;> ring
    have hv : v ∈ U := by
      have hm := U.sub_mem (closed x hx s hs) (U.smul_mem (2*x 0) hs)
      rw [ht] at hm
      exact (Submodule.smul_mem_iff U (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))).mp hm
    have hew : s - (4*x 0*x 2) • v = (2*x 0^2) • w := by
      ext i; fin_cases i <;> dsimp [s,mul,v,w] <;> ring
    have hw : w ∈ U := by
      have hm := U.sub_mem hs (U.smul_mem (4*x 0*x 2) hv)
      rw [hew] at hm
      exact (Submodule.smul_mem_iff U (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))).mp hm
    have heu : x - x 1 • v - x 2 • w = x 0 • u := by
      ext i; fin_cases i <;> dsimp [u,v,w] <;> ring
    have hu : u ∈ U := by
      have hm := U.sub_mem (U.sub_mem hx (U.smul_mem (x 1) hv)) (U.smul_mem (x 2) hw)
      rw [heu] at hm
      exact (Submodule.smul_mem_iff U ha).mp hm
    exact top_of_basis_mem U hu hv hw
  have perfect : square ⊤ = ⊤ := by
    let U := square (⊤ : Submodule ℂ (A))
    have hvv : mul (u) (v) = (2 : ℂ) • v := by
      ext i; fin_cases i <;> dsimp [mul,u,v] <;> ring
    have hww : mul (u) (w) = (2 : ℂ) • (v + w) := by
      ext i; fin_cases i <;> dsimp [mul,u,v,w] <;> ring
    have huu : mul (u) (u) = (4 : ℂ) • u + (2 : ℂ) • w := by
      ext i; fin_cases i <;> dsimp [mul,u,w] <;> ring
    have hv : v ∈ U := by
      have h := product_mem_square (U := ⊤) (x := u) (y := v) (by trivial) (by trivial)
      rw [hvv] at h
      exact (Submodule.smul_mem_iff U (by norm_num : (2 : ℂ) ≠ 0)).mp h
    have hw : w ∈ U := by
      have h := product_mem_square (U := ⊤) (x := u) (y := w) (by trivial) (by trivial)
      rw [hww] at h
      have h' := (Submodule.smul_mem_iff U (by norm_num : (2 : ℂ) ≠ 0)).mp h
      simpa using U.sub_mem h' hv
    have hu : u ∈ U := by
      have h := product_mem_square (U := ⊤) (x := u) (y := u) (by trivial) (by trivial)
      rw [huu] at h
      have h' := U.sub_mem h (U.smul_mem (2 : ℂ) hw)
      have h'' : (4 : ℂ) • u ∈ U := by simpa using h'
      exact (Submodule.smul_mem_iff U (by norm_num : (4 : ℂ) ≠ 0)).mp h''
    exact top_of_basis_mem U hu hv hw
  have embed_injective : Function.Injective (embed) := by
    intro x y h
    have h0 : x 0=y 0 := by simpa [embed] using congrFun h 0
    have h1 : x 0+x 1=y 0+y 1 := by simpa [embed] using congrFun h 1
    have h2 : x 0+x 2=y 0+y 2 := by simpa [embed] using congrFun h 3
    ext i; fin_cases i
    · exact h0
    · change x 1 = y 1
      linear_combination h1-h0
    · change x 2 = y 2
      linear_combination h2-h0
  have embedding_preserves_product (x y : A) :
      ambientMul (embed x) (embed y) = embed (mul x y) := by
    ext i; fin_cases i <;> dsimp [ambientMul,embed,mul] <;>
      (try simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.head_cons,Matrix.tail_cons]) <;> ring
  have ambient_evolution (i j : Fin 5) (h : i ≠ j) :
      ambientMul (fun k => if k=i then 1 else 0) (fun k => if k=j then 1 else 0) = 0 := by
    have disjoint (k : Fin 5) :
        (if k = i then (1 : ℂ) else 0) * (if k = j then 1 else 0) = 0 := by
      by_cases hi : k = i
      · have hj : k ≠ j := fun hj => h (hi.symm.trans hj)
        simp only [if_pos hi, if_neg hj, mul_zero]
      · simp only [if_neg hi, zero_mul]
    ext k
    fin_cases k <;> dsimp [ambientMul] <;>
      simp only [mul_assoc, disjoint, mul_zero, add_zero, sub_zero]
  have ambient_product_mem {U : Submodule ℂ (E)} {x y : E}
      (hx : x ∈ U) (hy : y ∈ U) : ambientMul x y ∈ ambientSquare U :=
    Submodule.subset_span ⟨x,hx,y,hy,rfl⟩
  have ambient_perfect : ambientSquare (V) = V := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro z ⟨x,hx,y,hy,rfl⟩
      obtain ⟨a,rfl⟩ := hx
      obtain ⟨b,rfl⟩ := hy
      rw [embedding_preserves_product]
      exact LinearMap.mem_range_self _ _
    · have hle : square ⊤ ≤ (ambientSquare (V)).comap (embed) := by
        apply Submodule.span_le.mpr
        rintro z ⟨x,_,y,_,rfl⟩
        change embed (mul x y) ∈ ambientSquare (V)
        rw [← embedding_preserves_product]
        exact ambient_product_mem (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
      rw [perfect] at hle
      intro z hz
      obtain ⟨a,rfl⟩ := hz
      exact hle (by trivial)
  have ambient_generates (U : Submodule ℂ (E)) (hUV : U ≤ V)
      (closed : ∀ x ∈ U, ∀ y ∈ U, ambientMul x y ∈ U)
      (x : E) (hx : x ∈ U) (ha : x 0 ≠ 0) : U = V := by
    obtain ⟨a,he⟩ := hUV hx
    let C := U.comap (embed)
    have hac : a ∈ C := by change embed a ∈ U; rwa [he]
    have ha0 : a 0 ≠ 0 := by
      have h : (embed a) 0 = x 0 := congrFun he 0
      simpa [embed] using h.trans_ne ha
    have hC : C = ⊤ := by
      apply generates C _ a hac ha0
      intro b hb c hc
      change embed (mul b c) ∈ U
      rw [← embedding_preserves_product]
      exact closed _ hb _ hc
    apply le_antisymm hUV
    intro z hz
    obtain ⟨b,rfl⟩ := hz
    have h : b ∈ C := by rw [hC]; trivial
    exact h
  have ambient_minimal (U : Submodule ℂ (E))
      (hUV : U ≤ V) (hne : U ≠ ⊥) (hp : ambientSquare U = U) : U = V := by
    classical
    have hex : ∃ x ∈ U, x 0 ≠ 0 := by
      by_contra h
      have hz : ∀ x ∈ U, x 0 = 0 := by simpa using h
      have hs : ambientSquare U ≤ ⊥ := by
        apply Submodule.span_le.mpr
        rintro z ⟨x,hx,y,hy,rfl⟩
        change ambientMul x y = 0
        obtain ⟨a,hea⟩ := hUV hx
        obtain ⟨b,heb⟩ := hUV hy
        have ha : a 0=0 := by simpa [embed] using (congrFun hea 0).trans (hz x hx)
        have hb : b 0=0 := by simpa [embed] using (congrFun heb 0).trans (hz y hy)
        rw [← hea,← heb,embedding_preserves_product]
        have hm : mul a b=0 := by ext i; fin_cases i <;> simp [mul,ha,hb]
        rw [hm,map_zero]
      exact hne (bot_unique (by simpa [hp] using hs))
    obtain ⟨x,hx,ha⟩ := hex
    apply ambient_generates U hUV _ x hx ha
    intro a ha b hb
    rw [← hp]
    exact ambient_product_mem ha hb
  let μ : E →ₗ[ℂ] E →ₗ[ℂ] E :=
    { toFun := fun x =>
        { toFun := ambientMul x
          map_add' := by
            intro y z
            ext i
            fin_cases i <;> dsimp [ambientMul] <;> ring
          map_smul' := by
            intro a y
            ext i
            fin_cases i <;> dsimp [ambientMul] <;> ring }
      map_add' := by
        intro x y
        ext z i
        fin_cases i <;> dsimp [ambientMul] <;> ring
      map_smul' := by
        intro a x
        ext y i
        fin_cases i <;> dsimp [ambientMul] <;> ring }
  have hdim : Module.finrank ℂ V = 3 := by
    rw [V, LinearMap.finrank_range_of_inj embed_injective]
    simp [A]
  refine ⟨μ, Pi.basisFun ℂ (Fin 5), V, ?_, ?_, hdim, ?_, ?_⟩
  · simp [E]
  · intro i j hij
    change ambientMul ((Pi.basisFun ℂ (Fin 5)) i) ((Pi.basisFun ℂ (Fin 5)) j) = 0
    have basis_coordinates (i : Fin 5) :
        (Pi.basisFun ℂ (Fin 5)) i = fun k => if k = i then 1 else 0 := by
      funext k
      by_cases hk : k = i <;> simp [Pi.basisFun_apply, Pi.single, hk]
    rw [basis_coordinates, basis_coordinates]
    exact ambient_evolution i j hij
  · exact ambient_perfect
  · intro U hUV hne hp
    exact ambient_minimal U hUV hne hp

end D5.S3.QuadraticForms.EvolutionAlgebras.BareiRemarkThreeFive
