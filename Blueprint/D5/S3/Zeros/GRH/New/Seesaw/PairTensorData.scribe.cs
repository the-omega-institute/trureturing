using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class PairTensorDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair Tensor Data", H("Pair Tensor Data"),
        Blocks(
            Paragraph(Text("Integral branching pairing for interlacing weights; definite periods as class sums, norm bound. Names for spaces, characters, levels, lifts and descents on the two grids.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/PairTensorData.levelIndex_eq_untwisted"),
                H("levelIndex_eq_untwisted"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("In grid Z, and in grid V for a ≠ 0, the index of the level at node (a, b) is the order of GL of its rank over O_E/𝔟, so it is free of ϑ.")))))));
}
