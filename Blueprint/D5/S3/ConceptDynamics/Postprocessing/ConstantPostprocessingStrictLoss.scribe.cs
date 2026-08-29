using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Postprocessing;

internal sealed class ConstantPostprocessingStrictLossDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Postprocessing/ConstantPostprocessingStrictLoss.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant postprocessing strictly loses every witnessed distinction.",
        H("Constant Postprocessing Strict Loss"),
        Blocks(Describe.Lean(
            DescribeId.Create("constant-postprocessing-strictly-enlarges-the-kernel"),
            DeclarationHandle.Create(
                Prefix + "constant_postprocessing_strictly_enlarges_kernel"),
            H("Constant postprocessing strictly enlarges the kernel"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take a readout that separates a displayed pair x and y, and replace every "
                        + "readout value by one fixed processed value.")),
                Paragraph(Text(
                    "All original collisions remain collisions after postprocessing, while the "
                        + "witness pair becomes a new collision.")),
                Paragraph(Text(
                    "The conclusion is strict kernel inclusion from that witness. It does not "
                        + "assert that the original readout is globally injective."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula q = F.Id("q");
        Formula collapsed = F.Id("c");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula constant = Seq(F.Id("value"), Sp, Mapsto, Sp, collapsed);
        return Disp(Seq(
            Forall, Sp, q, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            collapsed, Colon, Sp, F.Id("Z"), Comma, Sp,
            x, Comma, Sp, y, Colon, Sp, F.Id("X"), Comma, Sp,
            Call("q", x), Sp, Neq, Sp, Call("q", y), Sp, Rightarrow, Sp,
            Call("ker", q), Sp, Lt, Sp,
            Call("ker", Seq(constant, Sp, Circ, Sp, q)), Dot));
    }
}
