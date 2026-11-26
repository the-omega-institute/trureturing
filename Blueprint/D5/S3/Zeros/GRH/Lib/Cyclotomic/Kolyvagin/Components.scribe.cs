using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cyclotomic.Kolyvagin;

internal sealed class ComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Components", H("Components"),
        Blocks(
            Paragraph(Text("Locally constant cocycles for a character with vanishing conditions; the odd component.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cyclotomic/Kolyvagin/Components.component"),
                H("component"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The locally constant O/l^ν-valued cocycles for (cyc^eψ)⁻¹ vanishing at cmConj, on inertia over ℚ(μ_N) away from l, and on decomposition groups over ℚ(μ_{Nl^∞}) above l.")))))));
}
