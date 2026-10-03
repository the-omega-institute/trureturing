using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class RothDecompositionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hasse derivative matrix determinant factors through the Roth decomposition.",
        H("Roth Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("roth-decomposition"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/RothDecomposition.det_hasseDerivMatrix"),
            H("Roth Decomposition"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A Hasse derivative matrix determinant factors through the Roth decomposition."))),
            DescribeRole.Theorem))));
}
