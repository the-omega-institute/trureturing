using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class AuxiliaryPolynomialDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct a nonzero auxiliary polynomial with bounded index and logarithmic height.",
        H("Auxiliary Polynomial"),
        Blocks(Describe.Lean(
            DescribeId.Create("auxiliary-polynomial"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/AuxiliaryPolynomial.exists_ne_zero_le_index_logHeight_le"),
            H("Auxiliary Polynomial"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Construct a nonzero auxiliary polynomial with bounded index and logarithmic height."))),
            DescribeRole.Theorem))));
}
