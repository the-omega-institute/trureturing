using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingResidualGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete residual-coordinate overlap gives the complete normalized Gram matrix.",
        H("Padding Residual Gram"),
        Blocks(Describe.Lean(
            DescribeId.Create("padding-residual-gram"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/PaddingResidualGram.phi_gram"),
            H("Padding Residual Gram"),
            StatementSource.FromAuthor(EndpointFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite alphabet, arbitrary natural capacities encoded by a, and every head, the Gram matrix of the legal normalized padding vectors is G(a,head). A nonzero tail contributes exactly at its whole-tail coordinate and at head indices bounded by the residual head count. The common coordinates of two residuals stop at their minimum head count.")),
                Paragraph(Text("Equal tails give the corresponding minimum-head word multiplicity, and distinct tails give zero. The last-tail masses telescope, including the sink and tail-free cases. After normalization, comparable residuals have the square-root multiplicity ratio times their tail moment; reversed comparisons use complex conjugation and incomparable pairs vanish."))),
            DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        Formula a = F.Id("a");
        Formula head = F.Id("head");
        return Disp(Seq(Call("gram", Call("phi", a, head)), Sp, Eq, Sp, Call("G", a, head)));
    }
}
