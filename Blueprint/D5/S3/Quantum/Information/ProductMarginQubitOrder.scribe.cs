using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class ProductMarginQubitOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct pure-factor boundary", H("ProductMarginQubitOrder"), Blocks(
            Describe.Lean(DescribeId.Create("common-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_trace_bound"),
                H("The closed-disk common-trace bound"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For independent local closed-disk coordinates with nonnegative x less than one, every complex PSD common lower matrix K of the two actual product margins has trace at most (1-s)/(1+s), where s is the square root of the product of the two reliabilities z squared divided by one minus x squared. The proof constructs an explicit identity split and evaluates its quadratic energy. A zero denominator forces a pure local factor, handled by the annihilating split below. Neither K nor the individual product margins are required to be invertible, and K need not commute with them. The exceptional x=1 factors require the separate product-state entropy argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pure-common-lower"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginQubitOrder.common_lower_zero_of_pure_left"),
                H("The distinct pure-factor boundary"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For x nonnegative and less than one and x squared plus z squared equal to one, every PSD common lower matrix of the two stated tensor margins is zero. The other local matrices are arbitrary. An explicit complex split U+V=I annihilates the respective pure local margins. The split-energy bound then gives K at most zero, while positivity gives the reverse inequality. The argument does not invert K and imposes no commutation or real-entry restriction on it."))), DescribeRole.Theorem))));
}
