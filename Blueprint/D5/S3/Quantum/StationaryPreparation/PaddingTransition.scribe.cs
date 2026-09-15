using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingTransitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recoverable predecessors make the explicit last-tail transition an isometry.",
        H("Padding Transition"),
        Blocks(Describe.Lean(
            DescribeId.Create("padding-transition-gram"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/PaddingTransition.W_gram"),
            H("Padding Transition"),
            StatementSource.FromAuthor(EndpointFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite alphabet, every multiset a and every chosen head, W(a,head) has orthonormal columns. No maximality or positive-capacity assumption is needed. Its memory is the sink together with each nonzero bounded tail and a bounded head index.")),
                Paragraph(Text("The probability law includes the one-tail boundary: positive head index emits head, while index zero emits the sole tail letter into the sink. Zero-probability letters cannot produce supported predecessors. On nonzero support, the emitted letter and successor recover the entire predecessor; this recovery discharges the off-diagonal Gram entries."))),
            DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        Formula a = F.Id("a");
        Formula head = F.Id("head");
        return Disp(Seq(Call("conjTranspose", Call("W", a, head)), Sp, Call("W", a, head), Sp, Eq, Sp, D(1)));
    }
}
