using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReversePetzDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReversePetz.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary Petz factors of the six-dimensional reverse instance.",
        H("Positive amplitude and exact functional calculus"),
        Blocks(
            Entry("positive", "amplitude_positive", "A positive amplitude",
                "In the binary-times-three-level coordinate order, Y is the positive diagonal (1,2,2,1,2,2) plus the four rank-one squares from e0+e3, e1-e4, e0+e2, and e3-e5. In particular Y is invertible."),
            Entry("root", "output_root", "The output square root",
                "The physical channel output is Y squared divided by 62. Its positive square root is Y divided by sqrt(62), by uniqueness of the positive square root."),
            Entry("support", "output_support", "Full output support",
                "The output is positive definite, so its functional-calculus support is the identity. The spectral inverse square root is sqrt(62) times the inverse of Y."),
            Entry("kraus", "petz_kraus_identification", "The actual Petz operators",
                "For every one of the twelve environment labels, sqrt(rho) times the adjoint noise operator times the spectral inverse square root of the actual output equals the corresponding environment slice. Inactive labels give zero."),
            Entry("channel", "ordinary_petz_channel", "The ordinary reference-completed Petz channel",
                "A channel supplied by the reference-completed Petz construction acts on every physical output matrix as the slice Kraus sum and recovers rho from the actual noise output. Full support makes the reference completion term zero on every input."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
