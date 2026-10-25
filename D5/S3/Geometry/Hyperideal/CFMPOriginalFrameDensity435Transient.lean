import D5.S3.Geometry.Hyperideal.CFMPFrameContinuity435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativeMeasureBridge435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology
open Filter CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody

namespace CFMPOriginalFrameDensity435Transient

def originalDensity (l : Fin 6 → ℝ) (x : V) : ℝ :=
  Real.sqrt (-(lengthGram l).det) / (-gramQuadratic l (lift x))^2

theorem density_eq_original (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (x : V) :
    density M x = originalDensity l x := by
  have hs : |M.det| = Real.sqrt (-(lengthGram l).det) := by
    rw [CFMPActualGramJacobian435Transient.actual_frame_det_square M l hg,
      Real.sqrt_sq_eq_abs]
  have hq : q M x = -gramQuadratic l (lift x) := by
    simpa only [q, ambient, CFMPActualGramJacobian435Transient.radius,
      CFMPActualGramJacobian435Transient.framePoint,
      CFMPActualGramJacobian435Transient.lift3, lift] using
      CFMPActualGramJacobian435Transient.actual_radius_eq M l hg x
  simp only [density, originalDensity, hs, hq]

theorem original_density_continuity
    (l : ℝ → (Fin 6 → ℝ)) (M : ℝ → M4) (D : M4) (x : V) (t : ℝ)
    (hM : HasDerivAt M D t) (hd : (M t).det ≠ 0)
    (hg : ∀ᶠ s in 𝓝 t, ∀ i j, lorentz (M s i) (M s j) = lengthGram (l s) i j)
    (hq : q (M t) x ≠ 0) :
    HasDerivAt (fun s => originalDensity (l s) x)
      (divergence (fun z => originalDensity (l t) z •
        field (D * (M t)⁻¹) z) x) t := by
  have hgt := hg.self_of_nhds
  have hspace : originalDensity (l t) = density (M t) := by
    funext z
    exact (density_eq_original (M t) (l t) hgt z).symm
  rw [hspace]
  exact (frame_density_continuity M D x t hM hd hq).congr_of_eventuallyEq
    (hg.mono (fun s hs => (density_eq_original (M s) (l s) hs x).symm))

#print axioms original_density_continuity
end CFMPOriginalFrameDensity435Transient
