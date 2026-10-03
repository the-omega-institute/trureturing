using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class RothMovingChainDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A long moving chain of sufficiently strong approximants is impossible.",
        H("Roth Moving Chain"),
        Blocks(Describe.Lean(
            DescribeId.Create("roth-moving-chain"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/RothMovingChain.roth_no_moving_chain_aux"),
            H("Roth Moving Chain"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A long moving chain of sufficiently strong approximants is impossible."))),
            DescribeRole.Theorem))));
}
