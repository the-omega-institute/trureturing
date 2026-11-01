import D5.S3.HomologicalAlgebra.FinitePerturbation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open D5.S3.HomologicalAlgebra.FinitePerturbation
open D5.S3.HomologicalAlgebra.FinitePerturbation.Input
namespace FinitePerturbationCheck
abbrev U := ℂ × ℂ
abbrev V := U × U

def d0 : Module.End ℂ V where
  toFun x := ((0,0),(0,x.2.1))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

def h : Module.End ℂ V where
  toFun x := ((0,0),(x.2.2,0))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

def delta : Module.End ℂ V where
  toFun x := ((0,x.1.1),(0,x.1.1))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

def i : U →ₗ[ℂ] V where
  toFun x := (x,(0,0))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

def p : V →ₗ[ℂ] U := LinearMap.fst ℂ U U

private theorem input : ∃ c : Input (R := ℂ) (U := U) (V := V),
    c.d0 = d0 ∧ c.h = h ∧ c.delta = delta ∧ c.i = i ∧ c.p = p := by
  refine ⟨⟨d0,h,delta,i,p,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,rfl,rfl,rfl,rfl,rfl⟩ <;>
    ext x <;> simp [d0,h,delta,i,p,Module.End.mul_apply,LinearMap.comp_apply] <;> abel

noncomputable def model : Input (R := ℂ) (U := U) (V := V) :=
  Classical.choose input

private theorem binding : model.d0 = d0 ∧ model.h = h ∧ model.delta = delta ∧
    model.i = i ∧ model.p = p := Classical.choose_spec input

example : (model.h*model.delta)^2 = 0 := by
  rw [binding.2.1, binding.2.2.1, pow_two]
  ext x <;> simp [h,delta,Module.End.mul_apply]

example : delta ≠ 0 ∧ model.I 2 (1,0) = ((1,0),(-1,0)) ∧
    model.transferred 2 (1,0) = (0,1) ∧ model.transferred 2 ≠ 0 := by
  have bi := binding
  have lift : model.I 2 (1,0) = ((1,0),(-1,0)) := by
    simp [I,K,inversePolynomial,Finset.sum_range_succ,bi.2.1,bi.2.2.1,bi.2.2.2.1,h,delta,i]
  have transfer : model.transferred 2 (1,0) = (0,1) := by
    simp [transferred,lift,bi.2.2.1,bi.2.2.2.2,delta,p]
  refine ⟨?_,lift,transfer,?_⟩
  · intro eq
    have val := DFunLike.congr_fun eq ((1,0),(0,0))
    norm_num [delta] at val
  · intro eq
    have val := DFunLike.congr_fun eq (1,0)
    rw [transfer] at val
    norm_num at val
end FinitePerturbationCheck
