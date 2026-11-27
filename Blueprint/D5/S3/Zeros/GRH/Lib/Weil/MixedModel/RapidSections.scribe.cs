using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class RapidSectionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rapid Sections", H("Rapid Sections"),
        Blocks(
            Paragraph(Text("for ξ rapid, τ smooth of compact support and u smooth with unitary values, the vectors τ(x)ω₀(u(x))ξ are the slices of one rapid vector.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/RapidSections.exists_section"),
                H("exists_section"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For τ smooth of compact support, unitary u(x) depending smoothly on x, and ξ rapid, some rapid vector Φ has value τ(x)ω₀(u(x))ξ at every x in the mixed model.")))))));
}
