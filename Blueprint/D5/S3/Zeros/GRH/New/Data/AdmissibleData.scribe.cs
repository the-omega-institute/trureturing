using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Data;

internal sealed class AdmissibleDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissible Data", H("Admissible Data"),
        Blocks(
            Paragraph(Text("Record of admissible data; names for ranks, weights, the prime sum, the error budget and the cost of one direction.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Data/AdmissibleData.dirCost"),
                H("dirCost"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The cost of one direction: the sum over infinite places σ of jetSize(w₀(σ)) − primeSum(w(σ), σ), with Data.jetSize, Data.primeSum and the nominal weight w = Data.nominalWeight.")))))));
}
