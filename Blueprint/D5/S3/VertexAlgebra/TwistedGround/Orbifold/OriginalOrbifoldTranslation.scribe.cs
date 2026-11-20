using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OriginalOrbifoldTranslationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translation of the Original Orbifold Field",
        H("Translation of the Original Orbifold Field"),
        Blocks(
            Entry("translation", "T", "Diagonal translation",
                "Translation is the complex-linear endomorphism assembled from the fixed lattice translation "
                + "and the actual negative twisted translation.", DescribeRole.Definition),
            Entry("translation-on-states", "T_apply", "Translation on states",
                "Apply each sector translation to its component of the state."),
            Entry("vv-covariance", "vv_covariance", "Fixed-to-fixed covariance",
                "The fixed lattice commutator gives the normalized derivative coefficient."),
            Entry("vv-translation", "vv_translation", "Fixed-to-fixed source translation",
                "Specialize the fixed Borcherds identity to the zeroth stress mode to translate the source."),
            Entry("vm-translation", "vm_translation", "Fixed action on the negative sector",
                "Convert the physical derivative of the corrected field to the integer modes of the negative parity slice."),
            Entry("vm-covariance", "vm_covariance", "Fixed action covariance on the negative sector",
                "The commutator of the actual twisted translation with the corrected field restricts to the negative parity slice."),
            Entry("mm-translation", "mm_translation", "Twisted-to-fixed source translation",
                "In rank 24 the grade-wise inverse pairing carries the derivative of the normalized coefficient "
                + "to the original twisted-to-fixed mode."),
            Entry("mm-covariance", "mm_covariance", "Twisted-to-fixed covariance",
                "In rank 24, specialize the original mixed Jacobi identity to the zeroth stress mode."),
            Entry("mv-covariance", "mv_covariance", "Right-field covariance",
                "Reindex the finite original right sum and cancel the terms weighted by the summation index."),
            Entry("mv-translation", "mv_translation", "Right-field source translation",
                "Move the twisted translation through the finite original right sum using the fixed-action commutator and derivative."),
            Entry("field-translation", "Y_translation", "Derivative of the assembled field",
                "For the positive definite rank-24 lattice, the mode of the translated source is the mode at index n minus one "
                + "multiplied by minus n."),
            Entry("field-covariance", "Y_covariance", "Covariance of the assembled field",
                "For the positive definite rank-24 lattice, the commutator with diagonal translation has the same derivative coefficient."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
