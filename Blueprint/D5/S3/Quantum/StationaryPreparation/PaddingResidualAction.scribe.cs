using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingResidualActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual padding transition erases each emitted letter from the residual.",
        H("Padding Residual Action"),
        Blocks(Describe.Lean(
            DescribeId.Create("padding-residual-intertwining"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/PaddingResidualAction.padding_residual_intertwining"),
            H("Padding Residual Action"),
            StatementSource.FromAuthor(EndpointFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite alphabet, every multiset a, every chosen head, every nonzero residual r contained in a, every letter i and every memory coordinate k, the letter-i component of W padding(r) equals padding(r.erase(i)) at k if i is present, and equals zero otherwise. The head need not have maximum count.")),
                Paragraph(Text("The proof computes the transition on the actual residual coordinates: head reindexing, tail decrement, the one-tail sink, absent letters and tail-free residuals. For a nonzero residual, the letter-i component is the erased residual when i is present and zero otherwise. The tensor-coordinate identity identifies this action with the prescribed square-root-weighted image. The full attainment proof uses these inner products to preserve every finite complex linear relation before constructing V and U."))),
            DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        Formula a = F.Id("a");
        Formula head = F.Id("head");
        Formula r = F.Id("r");
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        return Disp(Seq(
            Call("coordinate", Call("mulVec", Call("W", a, head),
                Call("padding", a, head, r)), Call("pair", i, k)), Sp, Eq, Sp,
            Call("if", Call("member", i, r),
                Call("coordinate", Call("padding", a, head, Call("erase", r, i)), k), D(0))));
    }
}
