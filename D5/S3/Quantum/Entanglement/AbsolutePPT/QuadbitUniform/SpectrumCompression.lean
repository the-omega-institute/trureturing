/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Three boundary rows, ordered step positions and rounded scalar target. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

-- These slots, including equal columns at different slots, are never quotiented.
def A : Matrix (Fin 3) (Fin 16) ℝ :=
  ![![-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3],
    ![-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4],
    ![-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2]]

-- Piecewise arithmetic makes the inverse slot map available without a search.
def positions (N j : ℕ) (q : Fin 16) : ℕ :=
  if q.val < 5 then q.val + 1 else
  if q.val = 5 then j else N - 10 + (q.val - 6) + 1

theorem positions_literal (N j : ℕ) (hN : 67 ≤ N) :
    positions N j = ![1,2,3,4,5,j,N-9,N-8,N-7,N-6,N-5,N-4,N-3,N-2,N-1,N] := by
  funext q
  fin_cases q <;> simp [positions] <;> omega

theorem positions_strict (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) : StrictMono (positions N j) := by
  intro q r hqr
  have hq := q.isLt
  have hr := r.isLt
  have hqr' : q.val < r.val := hqr
  dsimp [positions]
  split_ifs <;> omega

def target (N : ℕ) : ℝ :=
  let t : ℕ := (3*N+4)/8
  (9*(N : ℝ)+16*(t : ℝ))/(3*(N : ℝ)+2*(t : ℝ))^2

theorem target_nonneg (N : ℕ) : 0 ≤ target N := by
  dsimp [target]
  positivity

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
