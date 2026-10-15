/- GID: D5/S3/Quantum/Walks/CMV/Representation
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/CMV/Representation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Riesz moment and CMV identities for scale-four self-similarity. -/

/- admission_basis: escape-witness
   Module witness: mu_outside
   Direct frozen dependencies:
   D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail
     declaration statement_id: sha256:866d2544f66c1d06437a72737a30260611f3d3ad3546581a69fd50db1c634bb4
   D5.S3.Weil.Szego.CanonicalTransfer.szegoRho
     declaration statement_id: sha256:8155eeaa9dd1f2640bb6365ddd75a4cc9fdb1ac7d21883d8cba593787c925834
   D5.S3.Weil.Szego.CanonicalTransfer.szego_rho_pos
     declaration statement_id: sha256:b440986d62bb484d69935806c23cf6449a0f9f409fcb9c6371e31974b2b92c99
   WalkCore.mu_outside: proof_shape: content; escape_witness: CMV.Representation.WalkCore.psi_outside
     Direct frozen dependencies: tail, szegoRho; consumers: RieszWalkSelfSimilarity.ProbabilityBlocks.prob_finite.
   SpectralReduction.amplitude_spectral: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: tail, szegoRho; consumers: CMV.Representation.SpectralReduction.cumulative_projection.
   SpectralReduction.cumulative_projection: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: tail, szegoRho; consumers: RieszWalkSelfSimilarity.Scaling.cumulative_scale_four.
   BandedBridge.one_step_of_pair_relations: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: tail, szegoRho; consumers: RieszWalkSelfSimilarity.cumulative_scale_four.
   CMVFromGramParameters.pair_relations_of_parameters: proof_shape: content; escape_witness: Riesz.Moments.coeff_stable
     Direct frozen dependencies: tail, szegoRho, szego_rho_pos; consumers: RieszWalkSelfSimilarity.cumulative_scale_four.
   The source rho is szegoRho (Complex.ofReal (alpha k)), whose value is
   Real.sqrt (1-alpha k^2); no duplicate rho definition is introduced.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15854
-/

import D5.S3.Quantum.Walks.CMV.Geronimus

open LaurentPolynomial
noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.Representation.Walk
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
/-- Each block is copied from Section 2 in real coordinates. -/
def R (x : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if x = 0 then !![alpha 0, (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha 0 : ℂ)); (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha 0 : ℂ)) * alpha 1, -alpha 0 * alpha 1]
  else !![-alpha (2*x-1) * alpha (2*x), -alpha (2*x-1) * (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ));
          (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ)) * alpha (2*x+1), -alpha (2*x) * alpha (2*x+1)]

def P (x : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ)) * (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x+1) : ℂ)), -alpha (2*x) * (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x+1) : ℂ)); 0, 0]

def Q (x : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x-1) : ℂ)) * alpha (2*x), (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x-1) : ℂ)) * (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ))]

def step (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  let x := j / 2
  let i : Fin 2 := Fin.ofNat 2 j
  ∑ c : Fin 2, R x i c * v (2*x+c) +
    (if x = 0 then 0 else ∑ c : Fin 2, P (x-1) i c * v (2*(x-1)+c)) +
    ∑ c : Fin 2, Q (x+1) i c * v (2*(x+1)+c)

def psi : ℕ → ℕ → ℝ
  | 0 => Pi.single 0 1
  | t+1 => step (psi t)

def mu (t x : ℕ) : ℝ := psi t (2*x)^2 + psi t (2*x+1)^2

/-- Entries of the block walk, with the left boundary handled separately. -/
private theorem step_at_zero (v : ℕ → ℝ) :
    step v 0 = alpha 0 * v 0 + (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha 0 : ℂ)) * v 1 := by
  simp [step,Fin.ofNat,R,Q,Fin.sum_univ_two]

private theorem step_at_one (v : ℕ → ℝ) :
    step v 1 = (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha 0 : ℂ))*alpha 1*v 0 - alpha 0*alpha 1*v 1 +
      (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha 1 : ℂ))*alpha 2*v 2 + (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha 1 : ℂ))*(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha 2 : ℂ))*v 3 := by
  simp [step,Fin.ofNat,R,Q,Fin.sum_univ_two]
  ring

private theorem step_even (v : ℕ → ℝ) (x : ℕ) (hx : 1 ≤ x) :
    step v (2*x) =
      -alpha (2*x-1)*alpha (2*x)*v (2*x) -alpha (2*x-1)*(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ))*v (2*x+1) +
      (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*(x-1)) : ℂ))*(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*(x-1)+1) : ℂ))*v (2*(x-1)) -
      alpha (2*(x-1))*(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*(x-1)+1) : ℂ))*v (2*(x-1)+1) := by
  have h0 : x ≠ 0 := by omega
  simp [step,Fin.ofNat,R,P,Q,Fin.sum_univ_two,h0]
  ring

private theorem step_odd (v : ℕ → ℝ) (x : ℕ) (hx : 1 ≤ x) :
    step v (2*x+1) =
      (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ))*alpha (2*x+1)*v (2*x) -alpha (2*x)*alpha (2*x+1)*v (2*x+1) +
      (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*(x+1)-1) : ℂ))*alpha (2*(x+1))*v (2*(x+1)) +
      (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*(x+1)-1) : ℂ))*(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*(x+1)) : ℂ))*v (2*(x+1)+1) := by
  have h0 : x ≠ 0 := by omega
  have hdiv : (2*x+1)/2 = x := by omega
  have hmod : (2*x+1)%2 = 1 := by omega
  simp [step,Fin.ofNat,R,P,Q,Fin.sum_univ_two,h0,hdiv,hmod]
  ring


end D5.S3.Quantum.Walks.CMV.Representation.Walk
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.Representation.WalkCore
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk

private def L (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  let x := j/2
  if j%2=0 then alpha (2*x)*v (2*x)+(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ))*v (2*x+1)
  else (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ))*v (2*x)-alpha (2*x)*v (2*x+1)

private def M (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j=0 then v 0 else
  let x := (j-1)/2
  if j%2=1 then alpha (2*x+1)*v (2*x+1)+(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x+1) : ℂ))*v (2*x+2)
  else (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x+1) : ℂ))*v (2*x+1)-alpha (2*x+1)*v (2*x+2)

private theorem L_even (v : ℕ → ℝ) (x : ℕ) :
    L v (2*x) = alpha (2*x)*v (2*x)+(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ))*v (2*x+1) := by simp [L]

private theorem L_odd (v : ℕ → ℝ) (x : ℕ) :
    L v (2*x+1) = (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ))*v (2*x)-alpha (2*x)*v (2*x+1) := by
  have hdiv : (2*x+1)/2=x := by omega
  have hmod : (2*x+1)%2=1 := by omega
  simp [L,hdiv,hmod]

private theorem M_odd (v : ℕ → ℝ) (x : ℕ) :
    M v (2*x+1) = alpha (2*x+1)*v (2*x+1)+(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x+1) : ℂ))*v (2*x+2) := by
  have h0 : 2*x+1≠0 := by omega
  have hmod : (2*x+1)%2=1 := by omega
  simp [M,h0,hmod]

private theorem M_even (v : ℕ → ℝ) (x : ℕ) (hx : 1≤x) :
    M v (2*x) = (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x-1) : ℂ))*v (2*x-1)-alpha (2*x-1)*v (2*x) := by
  have h0 : 2*x≠0 := by omega
  have hdiv : (2*x-1)/2=x-1 := by omega
  have hidx : 2*(x-1)+1=2*x-1 := by omega
  have hidx' : 2*(x-1)+2=2*x := by omega
  simp [M,h0,hdiv,hidx,hidx']

/-- The transposed CMV convention is M L, in the paper's coordinates. -/
private theorem step_factorization (v : ℕ → ℝ) : step v = M (L v) := by
  funext j
  rcases Nat.even_or_odd j with ⟨x,rfl⟩ | ⟨x,rfl⟩
  · rw [←two_mul x]
    by_cases h0 : x=0
    · subst x; simp [step_at_zero,M,L]
    · have hx : 1≤x := by omega
      have hidx : 2*x-1=2*(x-1)+1 := by omega
      have hidx' : 2*(x-1)+1=2*x-1 := hidx.symm
      rw [step_even v x hx,M_even _ x hx,hidx,L_odd,L_even]
      rw [hidx']
      ring
  · by_cases h0 : x=0
    · subst x
      simp [step_at_one,M,L]
      ring
    · have hx : 1≤x := by omega
      have hidx : 2*x+2=2*(x+1) := by omega
      have hidx' : 2*(x+1)-1=2*x+1 := by omega
      rw [step_odd v x hx,M_odd,L_odd,hidx,L_even,hidx']
      ring

/-- Finite propagation for the actual Schur-defined walk. -/
private theorem psi_outside (t x : ℕ) (hx : t<x) : psi t (2*x)=0 ∧ psi t (2*x+1)=0 := by
  induction t generalizing x with
  | zero => simp [psi,Pi.single_apply,show 2*x≠0 by omega,show 2*x+1≠0 by omega]
  | succ t ih =>
    have hx1 : 1≤x := by omega
    have hc := ih x (by omega)
    have hp := ih (x-1) (by omega)
    have hn := ih (x+1) (by omega)
    change step (psi t) (2*x)=0 ∧ step (psi t) (2*x+1)=0
    rw [step_even _ x hx1,step_odd _ x hx1]
    simp [hc.1,hc.2,hp.1,hp.2,hn.1,hn.2]

theorem mu_outside (t x : ℕ) (hx : t<x) : mu t x=0 := by
  obtain ⟨hL,hR⟩ := psi_outside t x hx
  simp [mu,hL,hR]

end D5.S3.Quantum.Walks.CMV.Representation.WalkCore
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows LaurentPolynomial

/-- The exact finite bridge obligation. Its one-step clause is independent of
self-similarity: it identifies the Schur-defined operator with multiplication. -/
structure SpectralBridge (chi : ℕ → (LaurentPolynomial ℝ)) : Prop where
  zero : chi 0 = T 0
  orth : ∀ i j : ℕ, sigma (chi i) (chi j) = if i=j then 1 else 0
  span : ∀ Y : ℕ, Submodule.span ℝ (chi '' {j | j<2*Y+2}) = V Y
  one_step : ∀ q : (LaurentPolynomial ℝ), ∀ j : ℕ,
    sigma (chi j) (T (-1)*q) = step (fun k => sigma (chi k) q) j

def cumulative (n Y : ℕ) : ℝ := ∑ y ∈ Finset.range (Y+1), mu n y

private theorem paired_sum (n N : ℕ) :
    (∑ j ∈ Finset.range (2*N), psi n j ^ 2) =
      ∑ y ∈ Finset.range N, mu n y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega,Finset.sum_range_succ,
      Finset.sum_range_succ,ih,Finset.sum_range_succ]
    simp only [mu]
    ring

theorem amplitude_spectral {chi : ℕ → (LaurentPolynomial ℝ)} (hb : SpectralBridge chi) (t j : ℕ) :
    psi t j = sigma (chi j) (T (-(t:ℤ))) := by
  induction t generalizing j with
  | zero =>
    rw [Nat.cast_zero,neg_zero,←hb.zero,hb.orth]
    simp [psi,Pi.single_apply]
  | succ t ih =>
    change step (psi t) j = _
    have heq : psi t = fun k => sigma (chi k) (T (-(t:ℤ))) := funext ih
    rw [heq,←hb.one_step,←T_add]
    congr 2
    push_cast
    ring

/-- The paper's projection formula needs only finite orthonormality and a
one-step relation; no infinite spectral theorem or convergence is used. -/
theorem cumulative_projection {chi : ℕ → (LaurentPolynomial ℝ)} (hb : SpectralBridge chi) (n Y : ℕ) :
    ∃ h : (LaurentPolynomial ℝ), IsProjection sigma (V Y) (T (-(n:ℤ))) h ∧
      sigma h h = cumulative n Y := by
  obtain ⟨hp,hn⟩ := D5.S3.Quantum.Walks.CMV.SzegoRecurrence.ProjectionNorm.finite_orthonormal_projection
    sigma chi hb.orth (2*Y+2) (T (-(n:ℤ)))
  rw [hb.span] at hp
  refine ⟨_,hp,hn.trans ?_⟩
  simp only [←amplitude_spectral hb]
  change (∑ j ∈ Finset.range (2*Y+2), psi n j ^ 2) = _
  rw [show 2*Y+2=2*(Y+1) by omega,paired_sum]
  rfl


end D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.Representation.BandedBridge
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.FormSymmetries D5.S3.Quantum.Walks.CMV.Representation.WalkCore LaurentPolynomial

/-- The two local changes of basis in the elementary finite CMV argument. -/
structure PairRelations (chi xi : ℕ → (LaurentPolynomial ℝ)) : Prop where
  initial : chi 0=xi 0
  m_odd : ∀ x : ℕ, chi (2*x+1)=
    alpha (2*x+1) • xi (2*x+1)+(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x+1) : ℂ)) • xi (2*x+2)
  m_even : ∀ x : ℕ, 1≤x → chi (2*x)=
    (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x-1) : ℂ)) • xi (2*x-1)-alpha (2*x-1) • xi (2*x)
  l_even : ∀ x : ℕ, T 1*xi (2*x)=
    alpha (2*x) • chi (2*x)+(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ)) • chi (2*x+1)
  l_odd : ∀ x : ℕ, T 1*xi (2*x+1)=
    (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha (2*x) : ℂ)) • chi (2*x)-alpha (2*x) • chi (2*x+1)

private theorem l_coefficients {chi xi : ℕ → (LaurentPolynomial ℝ)} (h : PairRelations chi xi) (q : (LaurentPolynomial ℝ)) :
    (fun j => sigma (T 1*xi j) q)=L (fun j => sigma (chi j) q) := by
  funext j
  rcases Nat.even_or_odd j with ⟨x,rfl⟩ | ⟨x,rfl⟩
  · rw [←two_mul x,h.l_even,L_even]
    simp
  · rw [h.l_odd,L_odd]
    simp

private theorem m_coefficients {chi xi : ℕ → (LaurentPolynomial ℝ)} (h : PairRelations chi xi) (q : (LaurentPolynomial ℝ)) :
    (fun j => sigma (T 1*chi j) q)=M (fun j => sigma (T 1*xi j) q) := by
  funext j
  rcases Nat.even_or_odd j with ⟨x,rfl⟩ | ⟨x,rfl⟩
  · rw [←two_mul x]
    by_cases hx : x=0
    · subst x
      simp [h.initial,M]
    · have hx1 : 1≤x := by omega
      rw [h.m_even x hx1,M_even _ x hx1]
      simp [mul_sub,mul_smul_comm]
  · rw [h.m_odd,M_odd]
    simp [mul_add,mul_smul_comm]

/-- The local pair relations give the paper's full one-step spectral formula. -/
theorem one_step_of_pair_relations {chi xi : ℕ → (LaurentPolynomial ℝ)} (h : PairRelations chi xi)
    (q : (LaurentPolynomial ℝ)) (j : ℕ) :
    sigma (chi j) (T (-1)*q)=step (fun k => sigma (chi k) q) j := by
  rw [sigma_shift_adjoint 1]
  have hc := m_coefficients h q
  rw [l_coefficients h q,←step_factorization] at hc
  exact congrFun hc j


end D5.S3.Quantum.Walks.CMV.Representation.BandedBridge
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.Representation.CMVFromGramParameters
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramOPUC D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCStarRecurrence D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries D5.S3.Quantum.Walks.CMV.Representation.BandedBridge LaurentPolynomial

def alternate (j : ℕ) : (LaurentPolynomial ℝ) :=
  if j%2=0 then T (-((j/2:ℕ):ℤ))*normalizedPhi j
  else T (-((j/2:ℕ):ℤ)-1)*normalizedPhiStar j

private theorem alternate_even (k : ℕ) : alternate (2*k)=T (-(k:ℤ))*normalizedPhi (2*k) := by
  simp [alternate]

private theorem alternate_odd (k : ℕ) : alternate (2*k+1)=T (-(k:ℤ)-1)*normalizedPhiStar (2*k+1) := by
  have hm : (2*k+1)%2=1 := by omega
  have hd : (2*k+1)/2=k := by omega
  simp [alternate,hm,hd]

private theorem normalizedPhi_zero : normalizedPhi 0=T 0 := by
  have hp : phi 0=T 0 := by
    have h := polynomial_expansion 0 (phi_mem_window 0)
    have hc : coeffLM 0 (phi 0)=1 := phi_monic 0
    simpa [hc] using h
  have hm : D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment 0=1 := by
    rw [D5.S3.Quantum.Walks.Riesz.Moments.moment_at 0 0 (by norm_num)]
    simp [D5.S3.Quantum.Walks.Riesz.Moments.coeffRec]
  have hn : gramNorm 0=1 := by
    unfold gramNorm normSquare
    rw [hp,sigma,momentForm_T_T,sub_self,hm]
    norm_num
  simp [normalizedPhi,hn,hp]

/-- Once Geronimus identifies the parameters, every CMV block follows from
finite normalized polynomial recursion. -/
theorem pair_relations_of_parameters (hparam : ∀ n : ℕ, alpha n=verblunsky n) :
    PairRelations chi alternate := by
  have hrho : ∀ n : ℕ, (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha n : ℂ))=(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (verblunsky n : ℂ)) := by intro n; simp only [D5.S3.Weil.Szego.CanonicalTransfer.szegoRho,Complex.normSq_ofReal,D5.S3.Weil.Szego.CanonicalTransfer.szegoRho,Complex.normSq_ofReal,hparam]
  have hf : ∀ n : ℕ, T 1*normalizedPhi n=
      alpha n • normalizedPhiStar n+(D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha n : ℂ)) • normalizedPhi (n+1) := by
    intro n
    have h := normalized_szego n
    rw [←hparam n] at h
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h.symm)
  have hs : ∀ n : ℕ, normalizedPhiStar (n+1)=
      (D5.S3.Weil.Szego.CanonicalTransfer.szegoRho (alpha n : ℂ)) • normalizedPhiStar n-alpha n • normalizedPhi (n+1) := by
    intro n
    simpa only [hparam,hrho] using normalized_star_inverse n
  constructor
  · rw [chi_zero,alternate_even 0,normalizedPhi_zero]
    simp
  · intro k
    rw [chi_odd,alternate_odd,show 2*k+2=2*(k+1) by omega,alternate_even]
    have h := congrArg (fun p : (LaurentPolynomial ℝ) => T (-(k:ℤ)-1)*p) (hf (2*k+1))
    rw [←mul_assoc,←T_add,show -(k:ℤ)-1+1=-(k:ℤ) by ring] at h
    have he : -((k+1:ℕ):ℤ)=-(k:ℤ)-1 := by push_cast; ring
    rw [he]
    rw [show 2*k+1+1=2*(k+1) by omega] at h
    simpa only [mul_add,mul_smul_comm] using h
  · intro k hk
    have hi : 2*k-1=2*(k-1)+1 := by omega
    rw [chi_even,alternate_even,hi,alternate_odd]
    have h := congrArg (fun p : (LaurentPolynomial ℝ) => T (-(k:ℤ))*p) (hs (2*k-1))
    rw [show 2*k-1+1=2*k by omega] at h
    have he : -((k-1:ℕ):ℤ)-1=-(k:ℤ) := by rw [Nat.cast_sub hk]; norm_num
    rw [he,←hi]
    simpa only [mul_sub,mul_smul_comm] using h
  · intro k
    rw [alternate_even,chi_even,chi_odd]
    have h := congrArg (fun p : (LaurentPolynomial ℝ) => T (-(k:ℤ))*p) (hf (2*k))
    rw [←mul_assoc,←T_add] at h
    rw [←mul_assoc,←T_add,add_comm (1:ℤ) (-(k:ℤ))]
    simpa only [mul_add,mul_smul_comm] using h
  · intro k
    rw [alternate_odd,chi_even,chi_odd]
    have h := congrArg (fun p : (LaurentPolynomial ℝ) => T (-(k:ℤ))*p) (hs (2*k))
    have he : (1:ℤ)+(-(k:ℤ)-1)=-(k:ℤ) := by ring
    rw [←mul_assoc,←T_add,he]
    simpa only [mul_sub,mul_smul_comm] using h


end D5.S3.Quantum.Walks.CMV.Representation.CMVFromGramParameters
end
