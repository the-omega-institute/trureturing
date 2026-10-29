using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class ProductMarginQubitOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct pure-factor boundary", H("ProductMarginQubitOrder"), Blocks(
            Describe.Lean(DescribeId.Create("pure-common-lower"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_zero_of_pure_left"),
                H("The distinct pure-factor boundary"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For x nonnegative and less than one and x squared plus z squared equal to one, every PSD common lower matrix of the two stated tensor margins is zero. The other local matrices are arbitrary. An explicit complex split U+V=I annihilates the respective pure local margins. The split-energy bound then gives K at most zero, while positivity gives the reverse inequality. The argument does not invert K and imposes no commutation or real-entry restriction on it."))), DescribeRole.Theorem))));
}
