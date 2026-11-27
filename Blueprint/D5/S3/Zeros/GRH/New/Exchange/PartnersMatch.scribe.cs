using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class PartnersMatchDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partners Match", H("Partners Match"),
        Blocks(
            Paragraph(Text("Locally constant partner data are matched pairs.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/PartnersMatch.mem_matchingPairs"),
                H("mem_matchingPairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For tame χ, partners Φ, Ψ (IsPartner) with Ψ locally constant form a pair in matchingPairs.")))))));
}
