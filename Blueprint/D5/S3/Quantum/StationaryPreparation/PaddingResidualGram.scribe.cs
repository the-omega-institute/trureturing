using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingResidualGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete residual-coordinate overlap is the minimum-head word multiplicity.",
        H("Padding Residual Gram"),
        Blocks(Describe.Lean(
            DescribeId.Create("padding-residual-gram"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/PaddingResidualGram.padding_inner"),
            H("Padding Residual Gram"),
            StatementSource.FromAuthor(EndpointFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite alphabet, arbitrary natural capacities encoded by a, every head, and every pair b and c of submultisets of a, the inner product of padding(b) and padding(c) is determined by their common coordinates. A nonzero tail contributes exactly at its whole-tail coordinate and at head indices bounded by the residual head count. The common coordinates of two residuals stop at their minimum head count.")),
                Paragraph(Text("Equal tails give the corresponding minimum-head word multiplicity, and distinct tails give zero. The last-tail masses telescope, including the sink and tail-free cases. After normalization, comparable residuals have the square-root multiplicity ratio times their tail moment; reversed comparisons use complex conjugation and incomparable pairs vanish."))),
            DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        Formula a = F.Id("a");
        Formula head = F.Id("head");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula common = Call("headSlice", head, b,
            Call("min", Call("count", b, head), Call("count", c, head)));
        return Disp(Seq(
            Call("inner", Call("padding", a, head, b), Call("padding", a, head, c)),
            Sp, Eq, Sp,
            Call("if", Seq(Call("tailOcc", head, b), Sp, Eq, Sp,
                Call("tailOcc", head, c)), Call("M", common), D(0))));
    }
}
