using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Postprocessing;

internal sealed class InjectivePostprocessingKernelEqualityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Postprocessing/InjectivePostprocessingKernelEquality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective postprocessing preserves an observation kernel exactly.",
        H("Injective Postprocessing Kernel Equality"),
        Blocks(Describe.Lean(
            DescribeId.Create("injective-postprocessing-preserves-pointwise-kernel-membership"),
            DeclarationHandle.Create(Prefix + "injective_postprocessing_preserves_kernel"),
            H("Injective postprocessing preserves pointwise kernel membership"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let q be a readout and p an injective postprocessing map. Fix two source "
                        + "states x and y.")),
                Paragraph(Text(
                    "Equality before processing is preserved by p, while equality after "
                        + "processing is reflected by injectivity of p.")),
                Paragraph(Text(
                    "The theorem is pointwise in x and y and therefore states exactly the "
                        + "equivalence of their original and processed kernel memberships."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula conclusion = Seq(
            Call("Kernel", Seq(p, Sp, Circ, Sp, q), x, y), Sp, Iff, Sp,
            Call("Kernel", q, x, y));
        return Disp(Seq(
            Forall, Sp, q, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            p, Colon, Sp, Arrow(F.Id("Y"), F.Id("Z")), Comma, Sp,
            x, Comma, Sp, y, Colon, Sp, F.Id("X"), Comma, Sp,
            Call("Injective", p), Sp, Rightarrow, Sp,
            Open, conclusion, Close, Dot));
    }
}
