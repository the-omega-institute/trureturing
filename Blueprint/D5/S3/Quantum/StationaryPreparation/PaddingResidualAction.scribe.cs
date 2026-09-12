using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PaddingResidualActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual padding transition preserves the prescribed image inner products.",
        H("Padding Residual Action"),
        Blocks(Describe.Lean(
            DescribeId.Create("padding-prescribed-image-gram"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/PaddingResidualAction.prescribed_image_gram"),
            H("Padding Residual Action"),
            StatementSource.FromAuthor(EndpointFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let the finite alphabet be nonempty, let a have arbitrary natural capacities, and choose a maximum-count head. For every pair of legal residuals r and s, image(a,head,r) and image(a,head,s) have the same inner product as the corresponding normalized padding vectors. The zero residual emits head into the common sink.")),
                Paragraph(Text("The proof computes the transition on the actual residual coordinates: head reindexing, tail decrement, the one-tail sink, absent letters and tail-free residuals. For a nonzero residual, the letter-i component is the erased residual when i is present and zero otherwise. The tensor-coordinate identity identifies this action with the prescribed square-root-weighted image. The full attainment proof uses these inner products to preserve every finite complex linear relation before constructing V and U."))),
            DescribeRole.Theorem))));

    private static Formula EndpointFormula()
    {
        Formula a = F.Id("a");
        Formula head = F.Id("head");
        return Disp(Seq(Call("inner", Call("image", a, head, F.Id("r")), Call("image", a, head, F.Id("s"))), Sp, Eq, Sp, Call("inner", Call("phi", a, head, F.Id("r")), Call("phi", a, head, F.Id("s")))));
    }
}
