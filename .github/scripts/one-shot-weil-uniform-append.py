from pathlib import Path
import re

root = Path('.')
path = root / 'D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.lean'
text = path.read_text()
names = ['reflectionRep', 'gamma_injective', 'reflectionRep_freq',
         'reflectionRep_eq_or', 'reflectionRep_image_sep',
         'zeroSummand_summable_of_zeroData', 'exists_quarter_power_mul_lt',
         'zeroSum_eq_tsum_of_zeroData']
for name in names:
    pattern = r'(?m)^private ((?:noncomputable )?(?:def|theorem) ' + re.escape(name) + r'\b)'
    text, count = re.subn(pattern, r'\1', text)
    if count != 1:
        raise RuntimeError(f'Expected exactly one private helper {name}, got {count}')
path.write_text(text)

path = root / 'D5/S3/Weil/ZetaBridge/FiniteEvenWeilOddInterpolation.lean'
text = path.read_text()
old = '''  Classical.choose (exists_even_weil_odd_interpolant F (frameDelta i))

@[simp]
theorem frameOddBasisTest_readout
    (F : FiniteEvenWeilOrbitFrame Z ι) (i j : ι) :
    frameOddReadout F (frameOddBasisTest F i) j = frameDelta i j :=
  Classical.choose_spec
    (exists_even_weil_odd_interpolant F (frameDelta i)) j'''
new = '''  Classical.choose (exists_even_weil_frame_interpolant F (frameDelta i))

/-- The basis is selected from the stronger two-sided interpolation theorem.
This retains zero even channel, rather than forgetting it behind odd readout. -/
theorem frameOddBasisTest_target_values
    (F : FiniteEvenWeilOrbitFrame Z ι) (i j : ι) :
    fourierLaplace (frameOddBasisTest F i) (Z.gamma (F.index j)) = frameDelta i j ∧
      fourierLaplace (frameOddBasisTest F i) (conj (Z.gamma (F.index j))) =
        -frameDelta i j :=
  Classical.choose_spec (exists_even_weil_frame_interpolant F (frameDelta i)) j

@[simp]
theorem frameOddBasisTest_readout
    (F : FiniteEvenWeilOrbitFrame Z ι) (i j : ι) :
    frameOddReadout F (frameOddBasisTest F i) j = frameDelta i j := by
  rw [frameOddReadout, oddSpectralChannel,
    (frameOddBasisTest_target_values F i j).1,
    (frameOddBasisTest_target_values F i j).2]
  ring'''
if text.count(old) != 1:
    raise RuntimeError('Signed-basis replacement does not match inspected source')
text = text.replace(old, new)
marker = '/-- The reduced negative sesquilinear form carried by the observable odd'
extra = '''/-- Full signed values of the finite synthesis. In particular the target
 even component vanishes, a stronger property than odd readout alone. -/
theorem frameOddSynthesis_target_values
    (F : FiniteEvenWeilOrbitFrame Z ι) (a : ι → ℂ) (j : ι) :
    fourierLaplace (frameOddSynthesis F a) (Z.gamma (F.index j)) = a j ∧
      fourierLaplace (frameOddSynthesis F a) (conj (Z.gamma (F.index j))) = -a j := by
  constructor
  · rw [frameOddSynthesis, fourierLaplace_finiteWeilLinearCombination]
    have hval (i : ι) :
        fourierLaplace (frameOddBasisTest F i) (Z.gamma (F.index j)) = frameDelta i j :=
      (frameOddBasisTest_target_values F i j).1
    simp_rw [hval]
    simp [frameDelta]
  · rw [frameOddSynthesis, fourierLaplace_finiteWeilLinearCombination]
    have hval (i : ι) :
        fourierLaplace (frameOddBasisTest F i) (conj (Z.gamma (F.index j))) =
          -frameDelta i j := (frameOddBasisTest_target_values F i j).2
    simp_rw [hval]
    simp [frameDelta]

'''
if text.count(marker) != 1:
    raise RuntimeError('Synthesis insertion anchor is not unique')
text = text.replace(marker, extra + marker)
path.write_text(text)

path = root / 'D5/S3/Weil/ZetaBridge/MultiOrbitBurnolUniformRemainder.lean'
text = path.read_text()
replacements = [
    ('    simp_rw [(P.killer_values _ j).1]', '''    have hkill (i : ι) : fourierLaplace (P.killer i)
        (Z.gamma (F.index j)) = frameDelta i j := (P.killer_values i j).1
    simp_rw [hkill]'''),
    ('    simp_rw [(P.killer_values _ j).2]', '''    have hkill (i : ι) : fourierLaplace (P.killer i)
        (conj (Z.gamma (F.index j))) = -frameDelta i j := (P.killer_values i j).2
    simp_rw [hkill]'''),
    ('  rw [h, orbitEvenEnergy, orbitOddEnergy, he, ho]\n  simp\n  ring',
     '  rw [h, orbitEvenEnergy, orbitOddEnergy, he, ho]\n  simp only [Complex.normSq_zero, mul_zero, zero_sub]\n  ring'),
    ('      exact_mod_cast (Z.multiplicity_pos (F.index i))',
     '      exact_mod_cast (Nat.succ_le_iff.mpr (Z.multiplicity_pos (F.index i)))'),
]
for old, new in replacements:
    if text.count(old) != 1:
        raise RuntimeError(f'Expected source reconciliation anchor exactly once: {old}')
    text = text.replace(old, new)
path.write_text(text)

modules = ['FiniteReflectionCompatibleWeilInterpolation', 'FiniteOrbitBurnolPacket',
           'FiniteMixedWeilMajorant', 'MultiOrbitBurnolUniformRemainder']
for name in modules:
    t = (root / f'D5/S3/Weil/ZetaBridge/{name}.lean').read_text()
    if re.search(r'\b(?:sorry|admit)\b|(?m:^\s*(?:axiom|unsafe)\b)', t):
        raise RuntimeError(f'Forbidden proof escape in {name}')

theory = root / 'docs/develop/theory/RH_RESEARCH_LANE_THEORY.md'
old_bytes = theory.read_bytes()
marker = b'## [PR #5065] UNIFORM_MULTI_ORBIT_BURNOL_REMAINDER'
if marker in old_bytes:
    raise RuntimeError('Theory marker already exists; refusing duplicate or replacement')
intro = '''

---

## [PR #5065] UNIFORM_MULTI_ORBIT_BURNOL_REMAINDER

Candidate formalization, 2026-09-05. No successful Lean compilation or axiom audit is claimed by this source-write operation. The reviewed development baseline was `a2412c6c5cbfdcf38145b6386ac54a3cdc536408`; the existing candidate frame APIs were read at `fcfc744126d37ede7750dbecc4b840b5a8923bd7`. This increment stays on the existing draft PR, without merge or rebase.

### Correction and library-first reuse

Scalar even Weil tests remain constant on multiplicity copies and under functional-equation reflection. The result concerns independently observable four-point orbit channels. Multiplicity sets a weight and margin, not extra scalar rank.

The earlier basis constructor chose a witness after forgetting its full signed values. It is now selected from `exists_even_weil_frame_interpolant`. The public `frameOddBasisTest_target_values` and `frameOddSynthesis_target_values` retain the exact +a/-a values and hence zero target even channel.

Eight previously private helper declarations in the existing single-orbit Burnol owner are made public with unchanged proof bodies. These supply the reflection quotient, gamma injectivity, sign separation, actual zero summability, geometric-depth choice, and equality of the symmetric zero sum with its ordinary tsum. They are reused rather than independently redefined.

### Closed finite-frame chain

The four owners below construct a common peak, a common finite exceptional ball, simultaneous signed killers, an absolutely summable majorant for ALL mixed terms, and finally a single common power depth at which every nonzero coefficient vector gives a negative FULL Weil zero sum.

For E(a)=sum_i |a_i|^2, the actual target union contributes -4 sum_i m_i |a_i|^2. The actual complement satisfies

`|R_N(a)| <= (1/4)^(N+1) C_basis E(a)`.

C_basis is the sum of the absolute mixed-convolution majorants. Its finiteness is proved from existing zeta summability. It depends on the fixed finite basis, but not on a or N. The power factor tends to zero. Since each analytic multiplicity is at least one, one common finite N suffices for strict negativity on the whole nonzero coefficient space.

This constructs a jointly localized basis. It does not assert that the older arbitrarily chosen fixed synthesis already had the full remainder estimate.

### Source-level details

'''
sections = []
for name in modules:
    source = (root / f'Blueprint/D5/S3/Weil/ZetaBridge/{name}.md').read_text()
    sections.append(f'#### `{name}`\n\n' + '\n'.join(source.splitlines()[2:]) + '\n')
end = '''
### Boundaries and next quantitative problems

A valid finite frame of nonreal off-line orbits is an input; existence of an off-line zero is never asserted. An empty frame is zero-dimensional. A nonempty frame is required for an actual negative test.

The constant and selected depth are classical and frame dependent. No computable estimate in minimum node separation, frame size, support radius, or height is established. Convolution depth may enlarge support. No uniform support window over all frames, infinite negative-index stability, prime-side coercivity, RH, or stronger zero-density theorem is claimed.

Next load-bearing goals are to package the actual full mixed Gram as a Hermitian matrix and identify its negative inertia with the realized test dimension, then derive explicit interpolation-conditioning and support-growth bounds and independently verifiable prime/Archimedean margins.
'''
theory.write_bytes(old_bytes + (intro + '\n'.join(sections) + end).encode('utf-8'))
assert theory.read_bytes().startswith(old_bytes)
assert theory.read_bytes().count(marker) == 1
(root / '.github/workflows/one-shot-weil-uniform-append.yml').unlink()
Path(__file__).unlink()
print('Existing proofs reused; signed basis strengthened; all prior theory bytes retained; transient automation removed.')
