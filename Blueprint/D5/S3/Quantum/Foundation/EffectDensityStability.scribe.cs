using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EffectDensityStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform approximate effect additivity yields one density with explicit dimension-dependent error.",
        H("Quantitative density stability on all effects"),
        Blocks(
            Paragraph(Text("Let d>=1, epsilon>=0 and p be an arbitrary total real function on actual Matrix (Fin d) (Fin d) Complex. An effect E has E.PosSemidef and (1-E).PosSemidef. Assume nonnegativity on every effect, p(identity)=1 and absolute binary defect at most epsilon for all positive semidefinite pairs with effect-valued sum.")),
            Paragraph(Text("Diagonal probes and real and imaginary pair probes give d squared positive matrices. Their total is at most (2*d-1) times the identity and every effect coordinate has absolute value at most 2*d-1. The signed-family estimate therefore gives a Hermitian candidate error eta=(2*d-1)^2*(6*d^2+1)*epsilon. The exact coordinate trace formula identifies the same candidate on every Hermitian matrix.")),
            Paragraph(Text("Nonnegativity and normalization give the two premises of uniform density repair. Its 3*eta correction combines with the candidate error to give 4*(2*d-1)^2*(6*d^2+1)*epsilon for one positive semidefinite rho with complex trace exactly one, simultaneously for every actual effect. This quantitative argument is the finite positive-coordinate construction with bounded interval stability and spectral repair.")),
            Paragraph(Text("Busch supplies the exact all-effect representation background. The quantitative estimate uses the global hypotheses stated here; finite observations alone do not establish them. No optimality, positive-error uniqueness or physical realization is asserted.")),
            Describe.Lean(
                DescribeId.Create("diagonal-probe"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.diagonalProbe"),
                H("diagonalProbe"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The diagonal probe is the matrix with a single one at the indicated diagonal coordinate.")),
                    Paragraph(Text("def diagonalProbe {d : ℕ} (i : Fin d) : Mat d := Matrix.single i i 1"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("real-probe"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.realProbe"),
                H("realProbe"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The real pair probe is one half of the outer product of e_i+e_j with its conjugate; effect claims below retain the distinct-index premise.")),
                    Paragraph(Text("def realProbe {d : ℕ} (i j : Fin d) : Mat d := (2 : ℂ)⁻¹ • Matrix.vecMulVec (Pi.single i 1 + Pi.single j 1) (star (Pi.single i 1 + Pi.single j 1))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imaginary-probe"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginaryProbe"),
                H("imaginaryProbe"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The imaginary pair probe is one half of the outer product of e_i+I*e_j with its conjugate, fixing the negative imaginary sign in its upper entry.")),
                    Paragraph(Text("def imaginaryProbe {d : ℕ} (i j : Fin d) : Mat d := (2 : ℂ)⁻¹ • Matrix.vecMulVec (Pi.single i 1 + Pi.single j Complex.I) (star (Pi.single i 1 + Pi.single j Complex.I))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("upper-entry"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.upperEntry"),
                H("upperEntry"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The upper candidate entry is formed from actual values on the real and imaginary pair probes and the mean of the two diagonal values.")),
                    Paragraph(Text("def upperEntry {d : ℕ} (p : Mat d → ℝ) (i j : Fin d) : ℂ := ⟨p (realProbe i j) - (p (diagonalProbe i) + p (diagonalProbe j))/2, (p (diagonalProbe i) + p (diagonalProbe j))/2 - p (imaginaryProbe i j)⟩"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("candidate"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.candidate"),
                H("candidate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every arbitrary real function on actual matrices, the candidate uses its diagonal probe values, the specified upper entries and conjugate lower entries.")),
                    Paragraph(Text("def candidate {d : ℕ} (p : Mat d → ℝ) : Mat d := fun i j => if i = j then (p (diagonalProbe i) : ℂ) else if i < j then upperEntry p i j else star (upperEntry p j i)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("candidate-hermitian"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.candidate_hermitian"),
                H("candidate hermitian"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The concrete candidate is Hermitian for every real function p and every natural dimension, without any positivity, normalization or additivity hypothesis.")),
                    Paragraph(Text("theorem candidate_hermitian {d : ℕ} (p : Mat d → ℝ) : (candidate p).IsHermitian"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-minus"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.realMinus"),
                H("realMinus"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The real complementary pair matrix is one half of the outer product of e_i-e_j with its conjugate.")),
                    Paragraph(Text("def realMinus {d : ℕ} (i j : Fin d) : Mat d := (2 : ℂ)⁻¹ • Matrix.vecMulVec (Pi.single i 1 - Pi.single j 1) (star (Pi.single i 1 - Pi.single j 1))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imaginary-minus"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginaryMinus"),
                H("imaginaryMinus"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The imaginary complementary pair matrix is one half of the outer product of e_i-I*e_j with its conjugate.")),
                    Paragraph(Text("def imaginaryMinus {d : ℕ} (i j : Fin d) : Mat d := (2 : ℂ)⁻¹ • Matrix.vecMulVec (Pi.single i 1 - Pi.single j Complex.I) (star (Pi.single i 1 - Pi.single j Complex.I))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("diagonal-eq"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_eq"),
                H("diagonal eq"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each diagonal probe is exactly the diagonal matrix of the corresponding coordinate indicator.")),
                    Paragraph(Text("theorem diagonal_eq {d : ℕ} (i : Fin d) : diagonalProbe i = Matrix.diagonal (fun k => if k = i then (1 : ℂ) else 0)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_effect"),
                H("diagonal effect"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every diagonal probe is an actual effect in every natural dimension for which its index exists.")),
                    Paragraph(Text("theorem diagonal_effect {d : ℕ} (i : Fin d) : IsEffect (diagonalProbe i)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-diagonal-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.pair_diagonal_le"),
                H("pair diagonal le"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the sum of the two diagonal probes is at most the identity in native matrix order.")),
                    Paragraph(Text("theorem pair_diagonal_le {d : ℕ} (i j : Fin d) (hij : i ≠ j) : diagonalProbe i + diagonalProbe j ≤ (1 : Mat d)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.real_complement"),
                H("real complement"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the sum of the diagonal probes minus the real pair probe equals its specified real complementary outer product.")),
                    Paragraph(Text("theorem real_complement {d : ℕ} (i j : Fin d) (hij : i ≠ j) : diagonalProbe i + diagonalProbe j - realProbe i j = realMinus i j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("imaginary-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_complement"),
                H("imaginary complement"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the sum of the diagonal probes minus the imaginary pair probe equals its specified imaginary complementary outer product.")),
                    Paragraph(Text("theorem imaginary_complement {d : ℕ} (i j : Fin d) (hij : i ≠ j) : diagonalProbe i + diagonalProbe j - imaginaryProbe i j = imaginaryMinus i j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-le-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.real_le_pair"),
                H("real le pair"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the real pair probe is bounded above by the sum of its diagonal probes.")),
                    Paragraph(Text("theorem real_le_pair {d : ℕ} (i j : Fin d) (hij : i ≠ j) : realProbe i j ≤ diagonalProbe i + diagonalProbe j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("imaginary-le-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_le_pair"),
                H("imaginary le pair"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the imaginary pair probe is bounded above by the sum of its diagonal probes.")),
                    Paragraph(Text("theorem imaginary_le_pair {d : ℕ} (i j : Fin d) (hij : i ≠ j) : imaginaryProbe i j ≤ diagonalProbe i + diagonalProbe j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.real_effect"),
                H("real effect"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the real pair probe and its identity complement are positive semidefinite.")),
                    Paragraph(Text("theorem real_effect {d : ℕ} (i j : Fin d) (hij : i ≠ j) : IsEffect (realProbe i j)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("imaginary-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_effect"),
                H("imaginary effect"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the imaginary pair probe and its identity complement are positive semidefinite.")),
                    Paragraph(Text("theorem imaginary_effect {d : ℕ} (i j : Fin d) (hij : i ≠ j) : IsEffect (imaginaryProbe i j)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entry-norm-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.entry_norm_bound"),
                H("entry norm bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every complex entry of every actual effect has complex norm at most one.")),
                    Paragraph(Text("theorem entry_norm_bound {d : ℕ} (E : Mat d) (hE : IsEffect E) (i j : Fin d) : ‖E i j‖ ≤ 1"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probe"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe"),
                H("probe"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The index pair selects a diagonal probe on the diagonal, a real pair probe above it and an imaginary pair probe below it.")),
                    Paragraph(Text("def probe {d : ℕ} (a : Fin d × Fin d) : Mat d := if a.1 = a.2 then diagonalProbe a.1 else if a.1 < a.2 then realProbe a.1 a.2 else imaginaryProbe a.2 a.1"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("probe-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_effect"),
                H("probe effect"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every member of this concrete indexed probe family is an actual effect.")),
                    Paragraph(Text("theorem probe_effect {d : ℕ} (a : Fin d × Fin d) : IsEffect (probe a)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probe-card"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_card"),
                H("probe card"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In every natural dimension the finite pair-index type has exactly d^2 members.")),
                    Paragraph(Text("theorem probe_card (d : ℕ) : Fintype.card (Fin d × Fin d) = d^2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.majorant"),
                H("majorant"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The majorant is the sum of the two indicated diagonal probes, with one duplicate removed on the diagonal.")),
                    Paragraph(Text("def majorant {d : ℕ} (a : Fin d × Fin d) : Mat d := diagonalProbe a.1 + diagonalProbe a.2 - if a.1 = a.2 then diagonalProbe a.1 else 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("probe-le-majorant"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_le_majorant"),
                H("probe le majorant"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every concrete probe is bounded above by its stated diagonal majorant.")),
                    Paragraph(Text("theorem probe_le_majorant {d : ℕ} (a : Fin d × Fin d) : probe a ≤ majorant a"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_sum"),
                H("diagonal sum"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The sum of all diagonal probes is the actual identity matrix, including the empty-dimensional identity convention.")),
                    Paragraph(Text("theorem diagonal_sum (d : ℕ) : (∑ i : Fin d, diagonalProbe i) = (1 : Mat d)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("triangular-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.triangular_sum"),
                H("triangular sum"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any finite linearly ordered index type and any additive commutative monoid, the double sum splits into its diagonal sum and paired strict-upper sum.")),
                    Paragraph(Text("theorem triangular_sum {ι A : Type*} [Fintype ι] [LinearOrder ι] [AddCommMonoid A] (f : ι → ι → A) : (∑ i, ∑ j, f i j) = (∑ i, f i i) + ∑ i, ∑ j, if i < j then f i j + f j i else 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("incident-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.incident_sum"),
                H("incident sum"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any finite index type and any real module with additive commutative monoid structure, the sum of incident scalar weights on the indexed vectors equals the double sum of pair weights on the corresponding vector sums.")),
                    Paragraph(Text("theorem incident_sum {ι A : Type*} [Fintype ι] [AddCommMonoid A] [Module ℝ A] (q : ι → ι → ℝ) (D : ι → A) : (∑ i, (∑ j, (q i j + q j i)) • D i) = ∑ i, ∑ j, q i j • (D i + D j)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate"),
                H("coordinate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The concrete real Hermitian coordinates use twice the real upper entry, minus twice its imaginary part, and the stated diagonal incident corrections.")),
                    Paragraph(Text("def coordinate {d : ℕ} (E : Mat d) (a : Fin d × Fin d) : ℝ := if a.1 = a.2 then (E a.1 a.1).re - ∑ k : Fin d, (if a.1 < k then (E a.1 k).re - (E a.1 k).im else if k < a.1 then (E k a.1).re - (E k a.1).im else 0) else if a.1 < a.2 then 2 * (E a.1 a.2).re else -2 * (E a.2 a.1).im"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("offdiag-term"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.offdiagTerm"),
                H("offdiagTerm"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each upper pair contributes its real and imaginary probe multiples with the diagonal correction subtracted.")),
                    Paragraph(Text("def offdiagTerm {d : ℕ} (E : Mat d) (i j : Fin d) : Mat d := (2 * (E i j).re) • realProbe i j + (-2 * (E i j).im) • imaginaryProbe i j - ((E i j).re - (E i j).im) • (diagonalProbe i + diagonalProbe j)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("offdiag-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.offdiag_identity"),
                H("offdiag identity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any actual complex matrix and distinct indices the corrected pair contribution is exactly its upper matrix unit plus the conjugate lower matrix unit.")),
                    Paragraph(Text("theorem offdiag_identity {d : ℕ} (E : Mat d) (i j : Fin d) (hij : i ≠ j) : offdiagTerm E i j = Matrix.single i j (E i j) + Matrix.single j i (star (E i j))"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-correction"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.upperCorrection"),
                H("upperCorrection"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The correction is the real part minus the imaginary part of an upper entry, and zero elsewhere.")),
                    Paragraph(Text("def upperCorrection {d : ℕ} (E : Mat d) (i j : Fin d) : ℝ := if i < j then (E i j).re - (E i j).im else 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coordinate-diagonal"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_diagonal"),
                H("coordinate diagonal"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The diagonal coordinate subtracts the sum of both incident upper corrections from the real diagonal entry, for every actual complex matrix.")),
                    Paragraph(Text("theorem coordinate_diagonal {d : ℕ} (E : Mat d) (i : Fin d) : coordinate E (i,i) = (E i i).re - ∑ j : Fin d, (upperCorrection E i j + upperCorrection E j i)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_pair"),
                H("coordinate pair"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two coordinates and probes of an upper pair split into the off-diagonal contribution and its diagonal correction, with the displayed conditional retained.")),
                    Paragraph(Text("theorem coordinate_pair {d : ℕ} (E : Mat d) (i j : Fin d) : (if i < j then coordinate E (i,j) • probe (i,j) + coordinate E (j,i) • probe (j,i) else 0) = (if i < j then offdiagTerm E i j else 0) + upperCorrection E i j • (diagonalProbe i + diagonalProbe j)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-split"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_split"),
                H("coordinate split"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every actual complex matrix the complete probe sum splits into its real diagonal contribution and the sum of corrected upper-pair contributions.")),
                    Paragraph(Text("theorem coordinate_split {d : ℕ} (E : Mat d) : (∑ a : Fin d × Fin d, coordinate E a • probe a) = (∑ i : Fin d, (E i i).re • diagonalProbe i) + ∑ i : Fin d, ∑ j : Fin d, if i < j then offdiagTerm E i j else 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-expansion"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_expansion"),
                H("coordinate expansion"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every actual Hermitian matrix is exactly the real linear combination of the concrete probes given by its coordinates; all natural dimensions are included.")),
                    Paragraph(Text("theorem coordinate_expansion {d : ℕ} (E : Mat d) (hE : E.IsHermitian) : (∑ a : Fin d × Fin d, coordinate E a • probe a) = E"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-probe-decomp"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.real_probe_decomp"),
                H("real probe decomp"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the real pair probe is one half of the sum of its four specified matrix units.")),
                    Paragraph(Text("lemma real_probe_decomp {d : ℕ} (i j : Fin d) (hij : i ≠ j) : realProbe i j = (2 : ℂ)⁻¹ • (Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j 1)"))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("imaginary-probe-decomp"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_probe_decomp"),
                H("imaginary probe decomp"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct indices the imaginary pair probe is one half of the four specified matrix units, with upper coefficient -I and lower coefficient I.")),
                    Paragraph(Text("lemma imaginary_probe_decomp {d : ℕ} (i j : Fin d) (hij : i ≠ j) : imaginaryProbe i j = (2 : ℂ)⁻¹ • (Matrix.single i i 1 + Matrix.single i j (-Complex.I) + Matrix.single j i Complex.I + Matrix.single j j 1)"))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("trace-single-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.trace_single_sum"),
                H("trace single sum"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any actual complex matrix C and complex scalar a, the complex trace of C times the indicated matrix unit is exactly a*C(j,i).")),
                    Paragraph(Text("lemma trace_single_sum {d : ℕ} (C : Mat d) (i j : Fin d) (a : ℂ) : Matrix.trace (C * Matrix.single i j a) = a * C j i"))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("trace-real-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.trace_real_formula"),
                H("trace real formula"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every actual complex C and distinct indices, its real trace pairing with the real pair probe is the stated mean of four real entries, without a Hermiticity hypothesis.")),
                    Paragraph(Text("lemma trace_real_formula {d : ℕ} (C : Mat d) (i j : Fin d) (hij : i ≠ j) : (Matrix.trace (C * realProbe i j)).re = ((C i i).re + (C j j).re + (C i j).re + (C j i).re) / 2"))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("trace-imaginary-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.trace_imaginary_formula"),
                H("trace imaginary formula"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every actual complex C and distinct indices, its real trace pairing with the imaginary pair probe is the stated combination of diagonal real parts and off-diagonal imaginary parts, without a Hermiticity hypothesis.")),
                    Paragraph(Text("lemma trace_imaginary_formula {d : ℕ} (C : Mat d) (i j : Fin d) (hij : i ≠ j) : (Matrix.trace (C * imaginaryProbe i j)).re = ((C i i).re + (C j j).re + (C j i).im - (C i j).im) / 2"))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("probe-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_trace"),
                H("probe trace"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every arbitrary real p the concrete Hermitian candidate reproduces p exactly on every probe through the real part of the actual complex trace.")),
                    Paragraph(Text("theorem probe_trace {d : ℕ} (p : Mat d → ℝ) (a : Fin d × Fin d) : (Matrix.trace (candidate p * probe a)).re = p (probe a)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_trace"),
                H("coordinate trace"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every arbitrary real p and every actual Hermitian H, the real part of the complex trace of candidate(p)*H equals the complete coordinate-weighted sum of p on the concrete probes. No probability premises on p are assumed.")),
                    Paragraph(Text("theorem coordinate_trace {d : ℕ} (p : Mat d → ℝ) (H : Mat d) (hH : H.IsHermitian) : (Matrix.trace (candidate p * H)).re = ∑ a : Fin d × Fin d, coordinate H a * p (probe a)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.majorant_sum"),
                H("majorant sum"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In every natural dimension the total diagonal majorant equals (2*d-1) times the actual identity, with d interpreted in the reals.")),
                    Paragraph(Text("theorem majorant_sum (d : ℕ) : (∑ a : Fin d × Fin d, majorant a) = (2 * (d : ℝ) - 1) • (1 : Mat d)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probe-sum-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.probe_sum_bound"),
                H("probe sum bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In every natural dimension the total concrete probe family is at most (2*d-1) times the actual identity in native matrix order.")),
                    Paragraph(Text("theorem probe_sum_bound (d : ℕ) : (∑ a : Fin d × Fin d, probe a) ≤ (2 * (d : ℝ) - 1) • (1 : Mat d)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_bound"),
                H("coordinate bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every d>=1 and every actual effect, every concrete real coordinate has absolute value at most 2*d-1, including dimension one.")),
                    Paragraph(Text("theorem coordinate_bound {d : ℕ} (hd : 1 ≤ d) (E : Mat d) (hE : IsEffect E) (a : Fin d × Fin d) : |coordinate E a| ≤ 2 * (d : ℝ) - 1"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("candidate-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.candidate_error"),
                H("candidate error"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every d>=1 and epsilon>=0, global effect nonnegativity, identity normalization and binary defect at most epsilon bound the error from p to the concrete candidate on every actual effect by (2*d-1)^2*(6*d^2+1)*epsilon.")),
                    Paragraph(Text("theorem candidate_error (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) (p : Mat d → ℝ) (hpos : ∀ E, IsEffect E → 0 ≤ p E) (hnorm : p 1 = 1) (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E + F) → |p (E + F) - p E - p F| ≤ ε) (E : Mat d) (hE : IsEffect E) : |p E - (Matrix.trace (candidate p * E)).re| ≤ (2 * (d : ℝ) - 1)^2 * (6 * (d : ℝ)^2 + 1) * ε"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("approximate-effect-density"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityStability.approximate_effect_density"),
                H("approximate effect density"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/busch2003effectprobabilities")),
                Blocks(
                    Paragraph(Text("For every natural d>=1, every real epsilon>=0 and every arbitrary real function p on actual complex d by d matrices, assume p is nonnegative on every actual effect, p(identity)=1, and absolute binary additive defect at most epsilon for all positive semidefinite E,F whose sum is an effect. There exists ONE actual positive semidefinite complex matrix rho with COMPLEX trace rho=1, such that for EVERY actual effect E the absolute difference between p(E) and Re(trace(rho*E)) is at most 4*(2*d-1)^2*(6*d^2+1)*epsilon, with d interpreted in the reals. The density is chosen before E. Epsilon zero and dimension one are included. No continuity, measurability, p(0)=0, commutativity, rank, small-error, supplied-coordinate, supplied-density or finite-sample premise is imposed.")),
                    Paragraph(Text("theorem approximate_effect_density (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) (p : Matrix (Fin d) (Fin d) ℂ → ℝ) (hpos : ∀ E : Matrix (Fin d) (Fin d) ℂ, E.PosSemidef → (1 - E).PosSemidef → 0 ≤ p E) (hnorm : p 1 = 1) (hadd : ∀ E F : Matrix (Fin d) (Fin d) ℂ, E.PosSemidef → F.PosSemidef → (E + F).PosSemidef ∧ (1 - (E + F)).PosSemidef → |p (E + F) - p E - p F| ≤ ε) : ∃ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ∀ E : Matrix (Fin d) (Fin d) ℂ, E.PosSemidef → (1 - E).PosSemidef → |p E - (Matrix.trace (ρ * E)).re| ≤ 4 * (2 * (d : ℝ) - 1)^2 * (6 * (d : ℝ)^2 + 1) * ε"))),
                DescribeRole.Theorem))));
}
