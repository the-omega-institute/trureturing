using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class NeutralThreeLegCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual output-projected finite neutral corrected-field coefficients and their raw normal-mode Laurent realization; the full Gaussian coefficient identity remains open.",
        H("Actual finite neutral-field coefficient bridge"),
        Blocks(
            Paragraph(Text("This unit proves output-projected finite mode restriction and finite scalar Laurent realization for the actual neutral correctedField, on the original tensor carrier. Source, input and output occupations may have arbitrary repetitions. The Gram matrix is the original raw matrix, the only invertibility assumption is the native hu, and rank zero is included.")),
            Paragraph(Text("The common finite mode set is {-k-1 : k is an output frequency} union {k : k is an input frequency}. Positive currents mix colours only at a fixed frequency. A negative mode outside the output frequency support can create a nonzero full vector, but its specified output coefficient vanishes. The support theorem therefore extracts that coefficient before restricting the sum.")),
            Paragraph(Text("The flat normal recursion is factored into creation multiplication on the left and Gram-weighted annihilation on the right. The proof uses the existing same-sign Heisenberg commutation law, the native monomial derivative and actual pointwise finite-support theorem. Ground vectors are carried by identity; no scalar ground vacuum is chosen.")),
            Paragraph(Text("The existing energy covariance supplies e = 2(E_T(output)-E_T(input)-E_S(source)), in doubled integral twisted-energy coordinates. The actual coefficients are represented by a finitely supported scalar Laurent polynomial. Evaluation is allowed only at a complex unit T and is a finite sum.")),
            Paragraph(Text("The raw source-output and source-input blocks are consumed in the actual finite evaluated normal-operator expansion. The source-specific bridge from finite Corr and this normal action to the factorial coefficient of exp(SS/2 + SO + SI + IO) remains unproved. In particular, the actual entry divided by source d! and input h!, with ordinary output coefficient, has not yet been identified with the full block GaussianCoefficient.")),
            Paragraph(Text("The intended remaining combinatorics is classical labelled-position Wick/Isserlis and the exponential formula: equal labels are distinct positions, so diagonal pairing counts have factors 2^m m! and off-diagonal counts m!. Wick (1950, Physical Review 80, 268) and Isserlis (1918, Biometrika 12, 134-139) supply the classical provenance; OriginalCorrectionGaussian supplies the repository actual Corr source-vacuum theorem. No new global novelty, positivity, unitarity, analytic completion, sewing, string-theory completion or AdS/CFT result is asserted.")),
            Describe.Lean(
                DescribeId.Create("native-neutral-source"),
                DeclarationHandle.Create(Prefix + "neutralSource"),
                H("Actual neutral source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The charge-zero carrier element is Finsupp.single 0 (monomial d 1), with arbitrary finite multiplicities."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-neutral-coefficient"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient"),
                H("Actual full corrected coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The field is correctedField on the existing ActualTensor carrier; no alternative Gaussian field is defined."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-neutral-expansion"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_native_expansion"),
                H("Actual Corr and pointwise normal expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite Corr support and residual polynomial support precede the native pointwise flatTerm finsum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-output-projection"),
                DeclarationHandle.Create(Prefix + "nativeOutputProjection"),
                H("Full ground-valued output coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial coefficient map is tensored with identity and composed with the canonical scalar tensor identification. Its result is the entire ground vector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-projected-support"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_projected_support"),
                H("Proved projected frequency support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every word, exponent, repeated input and output occupation, ground vector and mode tuple, a nonzero projected flatTerm implies membership of every mode in the common output-negative/input-positive frequency set. There is no vector-support hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-frequency-projected-mode-sum"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_frequency_projected_mode_sum"),
                H("Common finite projected mode sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each exponent and arbitrary ground vector, the output coefficient of the actual normal word equals the sum over the finite Cartesian mode box built from the output and input frequency supports."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-output-energy"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_output_energy_selection"),
                H("Actual corrected output exponent selection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full ground-valued corrected entry vanishes unless e equals oddWeight(output) minus oddWeight(input) minus twice the source weight. The proof consumes existing full-field energy covariance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-finite-projected-expansion"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_finite_projected_expansion"),
                H("Finite actual corrected entry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact output projection is a finite Corr shift, residual monomial and normal-mode sum. Its integer selector is retained; normal creation and annihilation act on the original polynomial input and the ground identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-laurent-coefficients"),
                DeclarationHandle.Create(Prefix + "nativeNeutralLaurentCoefficients"),
                H("Finite scalar Laurent entries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finitely supported integer coefficient function collects the actual Corr and normal-mode terms at their literal shifted exponents."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-laurent-identification"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_eq_laurent_coefficients"),
                H("Actual full field equals finite scalar entries times ground identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every integer exponent, source occupation, repeated input and output occupation, the actual projected correctedField coefficient is exactly the finite scalar Laurent coefficient multiplied by the arbitrary ground vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-laurent-entry"),
                DeclarationHandle.Create(Prefix + "nativeNeutralLaurentEntry"),
                H("Finite evaluation at a nonzero parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The evaluation parameter is a complex unit. Only the finite scalar coefficient function is evaluated, never an arbitrary Hahn series."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-laurent-ground-identity"),
                DeclarationHandle.Create(Prefix + "nativeNeutralLaurentEntry_ground_identity"),
                H("Finite evaluation retains the ground identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite scalar evaluation times any ground vector equals the finite Laurent-weighted sum of the actual projected correctedField coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-raw-normal-term"),
                DeclarationHandle.Create(Prefix + "nativeRawNormalTerm"),
                H("Raw mixed blocks in normal order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each negative mode uses the raw source-output Laurent coefficient as multiplication; each nonnegative mode uses the raw source-input coefficients as Gram-weighted derivatives. Every annihilation acts before the creation multiplications."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-raw-normal-expansion"),
                DeclarationHandle.Create(Prefix + "nativeNeutralLaurentEntry_raw_normal_expansion"),
                H("Actual Laurent entry consumes both raw mixed blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full actual finite Laurent entry equals the finite Corr shift and monomial expansion of these raw normal-mode operators. This is not yet the exponential coefficient of the full three-leg block matrix."))),
                DescribeRole.Theorem))));
}
