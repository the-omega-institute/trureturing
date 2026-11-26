using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar;

internal sealed class HaarMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Haar Mass", H("Haar Mass"),
        Blocks(
            Paragraph(Text("U(n) has total mass one; the measure on U(J) is right invariant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/HaarMass.isProbabilityMeasure_haarU"),
                H("isProbabilityMeasure_haarU"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("U(n) has mass 1 (the Cayley density has integral volU n): one column at a time.")))))));
}
