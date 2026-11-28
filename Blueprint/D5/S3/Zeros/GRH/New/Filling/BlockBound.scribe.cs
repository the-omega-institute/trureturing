using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class BlockBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block Bound", H("Block Bound"),
        Blocks(
            Paragraph(Text("Sum of inverse discriminant powers over classes and subspaces. Colouring count of kept near frames weighted by inverse index powers. Weighted count of near congruent pairs of terms, summed over classes, is bounded. Block amplitude bounded by a sum of sizes over kept near terms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/BlockBound.enorm_amplitudeSum_le_classSize"),
                H("enorm_amplitudeSum_le_classSize"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For the cut Bessel functions and stable T of level j, ‖A_T(c,s,c')‖ is at most the sum of ν·Filling.classSize j (Filling.classGauge) over near terms of T over (c,s,c') that represent their classes 𝖴⁰_c(g)γ𝖴⁰_c'(g), and is 0 unless s agrees.")))))));
}
