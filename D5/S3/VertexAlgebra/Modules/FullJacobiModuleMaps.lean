/- Source-only candidate: UNCOMPILED and UNACCEPTED.
The supplied FullJacobiIntertwiner has ModuleHom but no ModuleIso or Hom
operations. These operations retain its literal all-state/all-mode law.
No classification, positivity, dimension or nonzero-carrier assumption is used.
-/
import D5.S3.VertexAlgebra.Modules.FullJacobiIntertwiner

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Modules.FullJacobiIntertwiner
open FullJacobiCurrentTransport LatticeGeneratingFieldLocality
noncomputable section
universe u v w
variable {D : LatticeData} {M : Type u} {N : Type v} {P : Type w}
variable [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable [AddCommGroup P] [Module ℂ P]
variable {J : FullJacobiLatticeModule D M} {K : FullJacobiLatticeModule D N}
variable {L : FullJacobiLatticeModule D P}

def ModuleHom.id (J : FullJacobiLatticeModule D M) : ModuleHom J J where
  linearMap := LinearMap.id
  intertwines := by intro a n x; rfl

def ModuleHom.comp (g : ModuleHom K L) (f : ModuleHom J K) : ModuleHom J L where
  linearMap := g.linearMap.comp f.linearMap
  intertwines := by
    intro a n x
    simp only [LinearMap.comp_apply, f.intertwines, g.intertwines]

def ModuleHom.zero (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) : ModuleHom J K where
  linearMap := 0
  intertwines := by intro a n x; simp

def ModuleHom.add (f g : ModuleHom J K) : ModuleHom J K where
  linearMap := f.linearMap + g.linearMap
  intertwines := by
    intro a n x
    simp only [LinearMap.add_apply, map_add, f.intertwines, g.intertwines]

def ModuleHom.smul (c : ℂ) (f : ModuleHom J K) : ModuleHom J K where
  linearMap := c • f.linearMap
  intertwines := by
    intro a n x
    simp only [LinearMap.smul_apply, map_smul, f.intertwines]

/-- A full module isomorphism. The inverse intertwining law is a theorem,
not an additional endpoint assumption. -/
structure ModuleIso (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) where
  linearEquiv : M ≃ₗ[ℂ] N
  intertwines : ∀ (a : Carrier D) (n : ℤ) (x : M),
    linearEquiv (mode J a n x) = mode K a n (linearEquiv x)

def ModuleIso.hom (e : ModuleIso J K) : ModuleHom J K where
  linearMap := e.linearEquiv.toLinearMap
  intertwines := e.intertwines

theorem ModuleIso.inverse_intertwines (e : ModuleIso J K)
    (a : Carrier D) (n : ℤ) (y : N) :
    e.linearEquiv.symm (mode K a n y) =
      mode J a n (e.linearEquiv.symm y) := by
  apply e.linearEquiv.injective
  rw [e.linearEquiv.apply_symm_apply, e.intertwines,
    e.linearEquiv.apply_symm_apply]

def ModuleIso.inv (e : ModuleIso J K) : ModuleHom K J where
  linearMap := e.linearEquiv.symm.toLinearMap
  intertwines := e.inverse_intertwines

def ModuleIso.symm (e : ModuleIso J K) : ModuleIso K J where
  linearEquiv := e.linearEquiv.symm
  intertwines := e.inverse_intertwines

end
end D5.S3.VertexAlgebra.Modules.FullJacobiIntertwiner
