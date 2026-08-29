using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Postprocessing;

internal sealed class RecoverablePostprocessingKernelEqualityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Postprocessing/RecoverablePostprocessingKernelEquality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recoverable postprocessing preserves the readout kernel exactly.",
        H("Recoverable Postprocessing Kernel Equality"),
        Blocks(Describe.Lean(
            DescribeId.Create("recovery-on-the-readout-image-preserves-the-kernel"),
            DeclarationHandle.Create(
                Prefix + "recoverable_postprocessing_preserves_kernel"),
            H("Recovery on the readout image preserves the kernel"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let q be a readout, p a postprocessing map, and r a recovery map from "
                        + "processed values to original readout values.")),
                Paragraph(Text(
                    "Assume r(p(q(x))) = q(x) for every source state x. Recovery then reflects "
                        + "processed equality, while p preserves original equality.")),
                Paragraph(Text(
                    "The two equality kernels coincide. Recovery is required only on values in "
                        + "the image of q, not on every value of the output type."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula x = F.Id("x");
        Formula recovery = Seq(
            Forall, Sp, x, Colon, Sp, F.Id("X"), Comma, Sp,
            Call("r", Call("p", Call("q", x))), Sp, Eq, Sp, Call("q", x));
        return Disp(Seq(
            Forall, Sp, q, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            p, Colon, Sp, Arrow(F.Id("Y"), F.Id("Z")), Comma, Sp,
            r, Colon, Sp, Arrow(F.Id("Z"), F.Id("Y")), Comma, RowBreak, Grp(),
            Open, recovery, Close, Sp, Rightarrow, Sp,
            Call("ker", Seq(p, Sp, Circ, Sp, q)), Sp, Eq, Sp, Call("ker", q), Dot));
    }
}
