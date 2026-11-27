using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondPositivity4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPositivity4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positivity of the two signed ambient covariance operators.",
        H("Ambient covariance"),
        Blocks(
            Entry("massive-positive", "nullB_nonneg", "Massive covariance positivity",
                "The regulated shell squares are nonnegative. Their weak boundary limit is the quadratic form of the massive covariance on the dense profile embedding. Continuity extends the inequality to the entire Hilbert space, and self-adjointness gives operator positivity."),
            Entry("reflected-positive", "nullN_sub_J_nonneg", "Reflected covariance positivity",
                "Frequency reflection followed by conjugation preserves the real inner product, commutes with the massive correction, and reverses the sign of the skew multiplier. Transporting the positive quadratic form by this isometry gives the second signed positive bound."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
