using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bessel;

internal sealed class RealMeasuresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Measures", H("Real Measures"),
        Blocks(
            Paragraph(Text("Haar measure on unipotent subgroups is Lebesgue in free entries, bi-invariant, conjugation-invariant. Haar measures on the real unitary group are σ-finite.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bessel/RealMeasures.measurePreserving_freeEntries_besselHaar"),
                H("measurePreserving_freeEntries_besselHaar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The free entries (freeEntries at IsFreeEntry) carry the measure Shape.besselHaar on 𝖴 to Lebesgue measure.")))))));
}
