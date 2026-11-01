using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class NeutralThreeLegCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual corrected neutral field has a finite three-leg coefficient expansion with the literal Corr correction, repeated occupations, finite normal modes, and the native Gaussian correction readout.",
        H("Native finite neutral three-leg coefficient identity"),
        Blocks(
            Paragraph(Text(
                "The source is the actual correctedField on the full ActualTensor carrier. "
                + "For an arbitrary finite repeated oscillator occupation d, coefficient extraction first exposes the literal Corr support "
                + "and then expands each actual polynomial into the actual charged zero normal word. "
                + "The pointwise mode sum remains a finsum on the input tensor, so no endomorphism-valued infinite sum is introduced.")),
            Paragraph(Text(
                "The zero-charge seed is the existing identity field. Its flat coefficient is therefore the genuine creation-left, "
                + "annihilation-right normal product with the integer exponent selector. The correction is the supplied finite Corr, "
                + "whose repeated labelled occurrences retain all diagonal and off-diagonal matching multiplicities. "
                + "The source-vacuum linear-form readout is the actual Corr evaluation and gives the factorial Gaussian coefficient for every finite family.")),
            Paragraph(Text(
                "For a mode tuple, negative entries record output frequencies -k-1 and nonnegative entries record input frequencies k. "
                + "The frequency projection is the finite set {-k-1 | k is in the output support} union {k | k is in the input support}; "
                + "the Gram matrix only mixes colours at a fixed frequency. The native mode box theorem reduces the actual pointwise finsum "
                + "to this finite product once the literal support condition is supplied.")),
            Paragraph(Text(
                "The exponent theorem is proved before any scalar evaluation. Corr bidegree supplies shift plus residual source weight equals "
                + "the original source weight, the flat selector supplies the normal displacement, and the signed mode balance gives "
                + "e = 2(E_T(output)-E_T(input)-E_S(source)), expressed in Lean with doubled twisted energies. "
                + "Only after this finite regrouping may a nonzero T be substituted in the resulting Laurent monomial.")),
            Paragraph(Text(
                "The matching argument is the labelled-position Wick/Isserlis expansion: each new insertion either leaves its position unmatched "
                + "or pairs it with one earlier unmatched position, and the pair derivation vanishes on an already formed pair. "
                + "This is the finite algebraic bridge for arbitrary repeated occupations; it makes no analytic completion, whitening, damping, "
                + "unitarity, sewing, string-theory, or AdS/CFT claim.")),
            Paragraph(Text(
                "After the finite projection and exponent regrouping, the raw three-leg generating kernel is the exponential of the four actual "
                + "finite bilinear pieces: one half of the source-source covariance p_st G_ij T^(-2s-2t), the source-output creation symbol "
                + "J_s(-k-1) T^(2k-2s+1), the source-input annihilation symbol omega_k G_ij J_s(k) T^(-2k-2s-1), and the identity propagation term "
                + "eta_jk xi_jk. Source coefficients are divided by d!, input coefficients by h!, while output uses ordinary monomial coefficients; "
                + "the diagonal source pair contributes p_ss G_ii with no extra factor two.")),
            Describe.Lean(
                DescribeId.Create("native-neutral-source"),
                DeclarationHandle.Create(Prefix + "neutralSource"),
                H("Actual neutral source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source is the full carrier element with the requested arbitrary finite oscillator occupation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-neutral-coefficient-source"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_source"),
                H("Coefficient exposes correctedPolynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual corrected field reduces at charge zero to the literal correctedPolynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-neutral-expansion"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_native_expansion"),
                H("Finite actual Corr and normal-word expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equality keeps Corr support, polynomial support, actual chargedField normal words, repeated occurrences, and pointwise flatTerm mode sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-neutral-gaussian-readout"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCorrection_gaussian"),
                H("Actual Corr Gaussian readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing actual Corr source-vacuum readout is the factorial Gaussian coefficient for arbitrary finite linear forms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-mode-energy-balance"),
                DeclarationHandle.Create(Prefix + "native_mode_energy_balance"),
                H("Signed native mode energy balance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The negative output and nonnegative input occupations of every actual mode tuple satisfy the signed doubled-frequency balance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-exponent-regrouping"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_exponent_regrouping"),
                H("Native exponent regrouping"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Corr bidegree, the actual flat selector, and the signed mode balance prove the common finite Laurent exponent before evaluation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-projected-mode-sum"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_projected_mode_sum"),
                H("Finite projected actual mode sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual pointwise finsum equals the finite native mode box under the literal support condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-frequency-projected-mode-sum"),
                DeclarationHandle.Create(Prefix + "nativeNeutralCoefficient_frequency_projected_mode_sum"),
                H("Output/input frequency projected mode sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The projection is instantiated with the native frequency set {-k-1 from output} union {k from input}; no color support assumption is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-raw-kernel"),
                DeclarationHandle.Create(Prefix + "nativeNeutralRawKernel"),
                H("Explicit four-piece raw kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source-source, source-output, source-input, and identity-propagation terms are defined directly from pairScalar, jetScalar, frequency, G, and the Laurent powers of T."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-source-covariance"),
                DeclarationHandle.Create(Prefix + "nativeSourceSourceKernel_eq_covariance"),
                H("Source-source kernel is the native covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At T nonzero, the explicit source-source Laurent power is exactly the existing Corr covariance evaluated at T^-2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-raw-kernel-components"),
                DeclarationHandle.Create(Prefix + "nativeNeutralRawKernel_components"),
                H("Raw kernel component equality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four finite bilinear pieces are exposed as an equality, with the source-source diagonal carrying its one-half coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-finite-wick-identity"),
                DeclarationHandle.Create(Prefix + "nativeNeutralFiniteWickIdentity"),
                H("Finite repeated-occupation native Wick identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite labelled family and arbitrary occupation, the actual sourceVacuum Corr readout equals the exact factorial Gaussian coefficient."))),
                DescribeRole.Theorem))));
}
