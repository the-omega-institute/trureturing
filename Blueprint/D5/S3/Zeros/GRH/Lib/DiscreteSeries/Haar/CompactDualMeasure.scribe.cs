using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar;

internal sealed class CompactDualMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact Dual Measure", H("Compact Dual Measure"),
        Blocks(
            Paragraph(Text("Cayley chart density gives Haar measure on U(J); area inequality; invariance under isometries.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/CompactDualMeasure.measurePreserving_haarU"),
                H("measurePreserving_haarU"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let J, J' be hermitian involutions, a, b invertible, ε real nonzero, bᴴ(εJ)b = J'. A bijection φ: U(J) → U(J') given by g ↦ agb carries the measure haarU of U(J) to that of U(J').")))))));
}
