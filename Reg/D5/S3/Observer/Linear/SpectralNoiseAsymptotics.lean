import D5.S3.Observer.Linear.SpectralNoiseAsymptotics
import Reg.Support.DependentFamily
import Mathlib.Tactic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Topology BigOperators
noncomputable section
namespace Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics
abbrev Parameters := Σ (_ : ℝ), Σ (_ : ℝ), ℝ
abbrev signature : Signature where
  Params := Parameters
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def emptyAnchor : ∀ (_ : Empty) p,signature.State p := fun e => nomatch e
def actual : Realization signature := realize signature
  (fun _ p x => Real.log (1+x/(p.1*p.2.2^p.2.1))) emptyAnchor
def modified : Realization signature := realize signature (fun _ p _ => p.2.2⁻¹) emptyAnchor
def theoremLaw (family:Realization signature) : Prop := ∀ (n:ℕ) (q:Fin (n+1) → ℕ) (hq:∀ i,q i≤q (Fin.last n))
  (lam:ℝ → Fin (n+1) → ℝ) (c C β:ℝ) (hc:0<c) (hC:0<C) (hβ:0<β)
  (hbounds:∀ᶠ T:ℝ in 𝓝[>] 0,∀ i,c*T^(q i)≤lam T i ∧ lam T i≤C*T^(q i)) ,
 (∀ α:ℝ,
    (fun T:ℝ=>(1/2:ℝ)*(∑ i:Fin (n+1),family.readout () ⟨β,α,T⟩ (lam T i))-
      (1/2:ℝ)*(∑ i:Fin (n+1),max (α-(q i:ℝ)) 0)*Real.log (1/T))
      =O[𝓝[>] 0] (fun _:ℝ=>(1:ℝ))) ∧
  (∀ eps:ℝ → ℝ,(∀ T:ℝ,0<T → 0<eps T) →
    (Tendsto (fun T:ℝ=>(1/2:ℝ)*∑ i:Fin (n+1),eps T/(β*eps T+lam T i))
      (𝓝[>] 0) (𝓝 0) ↔ eps =o[𝓝[>] 0] (fun T:ℝ=>T^(q (Fin.last n))))) ∧
  (∀ α:ℝ,(∀ i,α≠(q i:ℝ)) →
    Tendsto (fun T:ℝ=>(1/2:ℝ)*∑ i:Fin (n+1),T^α/(β*T^α+lam T i))
      (𝓝[>] 0) (𝓝 ((1/2:ℝ)*∑ i:Fin (n+1),if α<(q i:ℝ) then β⁻¹ else 0)))
def arena : Arena where
  signature := signature
  Law := theoremLaw

theorem actual_law : arena.Law actual := by
  intro n q hq lam c C β hc hC hβ hbounds
  exact _root_.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.spectral_noise_asymptotics
    n q hq lam c C β hc hC hβ hbounds

theorem modified_law : ¬ arena.Law modified := by
  intro h
  have hb:∀ᶠ T:ℝ in 𝓝[>] 0,∀ i:Fin 1,(1:ℝ)*T^(0:ℕ)≤1 ∧ 1≤2*T^(0:ℕ):=
    Filter.Eventually.of_forall (by intro T i;norm_num)
  have hh:=h 0 (fun _=>0) (fun _=>le_rfl) (fun _ _=>1) 1 2 1
    zero_lt_one (by norm_num) zero_lt_one hb
  have hi:(fun T:ℝ=>(1/2:ℝ)*T⁻¹)=O[𝓝[>] 0] (fun _:ℝ=>(1:ℝ)):=by
    simpa [theoremLaw,modified,realize,Fin.sum_univ_one] using hh.1 0
  obtain ⟨K,hK⟩:=hi.bound
  have hTsmall:∀ᶠ T:ℝ in 𝓝[>] 0,T<(2*(|K|+1))⁻¹:=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds (inv_pos.mpr (by positivity)))
  have hpos : ∀ᶠ T : ℝ in 𝓝[>] 0, 0 < T := self_mem_nhdsWithin
  obtain ⟨T,hT,hs,hb⟩ := (hpos.and (hTsmall.and hK)).exists
  have hinv : 2*(|K|+1) < T⁻¹ := lt_inv_of_lt_inv₀ hT hs
  have habs : |(1/2:ℝ)*T⁻¹| ≤ K := by
    simpa only [Real.norm_eq_abs,norm_one,mul_one] using hb
  have hb' : (1/2:ℝ)*T⁻¹ ≤ K := (le_abs_self _).trans habs
  linarith [le_abs_self K]

theorem dependence_proof : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1,0,1⟩,1,2,?_⟩
  have hlog:Real.log 2<Real.log 3:=Real.log_lt_log (by norm_num) (by norm_num)
  norm_num [actual,realize]
  exact hlog.ne

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,modified,modified_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨modified,?_,rfl,modified_law⟩
      intro other hne
      exact (hne (by cases role;cases other;rfl)).elim
    · intro e;exact nomatch e
  dependence := dependence_proof


register_information_theorem _root_.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.spectral_noise_asymptotics in arena
  readout via (realize signature (fun _ p x => Real.log (1+x/(p.1*p.2.2^p.2.1))) emptyAnchor)
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics,
    coordinates := #[6,11,12],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "arg", "body"],
      stateOperand := some #["arg","arg","fn","arg"] }] })
  escape continues (open)
end Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics
