using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SensorFamilies;

internal sealed class PairReadoutKernelIntersectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/SensorFamilies/PairReadoutKernelIntersection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The kernel of a paired readout is the intersection of its two kernels.",
        H("Pair Readout Kernel Intersection"),
        Blocks(Describe.Lean(
            DescribeId.Create("the-paired-kernel-is-the-component-kernel-intersection"),
            DeclarationHandle.Create(Prefix + "pair_readout_kernel_eq_intersection"),
            H("The paired kernel is the component-kernel intersection"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Pair two arbitrary readouts left and right on the same source type.")),
                Paragraph(Text(
                    "Two states have equal paired readouts exactly when both component "
                        + "readouts are equal on those states.")),
                Paragraph(Text(
                    "Consequently the set of paired collisions is precisely the intersection "
                        + "of the two component collision sets."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula left = F.Id("left");
        Formula right = F.Id("right");
        Formula state = F.Id("x");
        Formula pair = Seq(state, Sp, Mapsto, Sp,
            Open, Call("left", state), Comma, Sp, Call("right", state), Close);
        return Disp(Seq(
            Forall, Sp, left, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            right, Colon, Sp, Arrow(F.Id("X"), F.Id("Z")), Comma, Sp,
            Call("ker", pair), Sp, Eq, Sp,
            Call("intersection", Call("ker", left), Call("ker", right)), Dot));
    }
}
