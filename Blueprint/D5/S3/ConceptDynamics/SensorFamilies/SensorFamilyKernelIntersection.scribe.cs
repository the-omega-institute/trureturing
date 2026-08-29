using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SensorFamilies;

internal sealed class SensorFamilyKernelIntersectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyKernelIntersection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A joint sensor kernel is the intersection of all coordinate kernels.",
        H("Sensor Family Kernel Intersection"),
        Blocks(Describe.Lean(
            DescribeId.Create("the-joint-readout-kernel-is-the-coordinate-intersection"),
            DeclarationHandle.Create(Prefix + "joint_readout_kernel_eq_iInter"),
            H("The joint-readout kernel is the coordinate intersection"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "View an indexed sensor family as one function-valued joint readout.")),
                Paragraph(Text(
                    "Equality of two joint readouts is equality at every sensor coordinate, "
                        + "and coordinatewise equality reconstructs equality of the functions.")),
                Paragraph(Text(
                    "Thus the joint collision set is the intersection over all coordinate "
                        + "kernels, including when the index type is empty or infinite."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula sensor = F.Id("sensor");
        Formula joint = Seq(F.Id("x"), Sp, Mapsto, Sp,
            Open, F.Id("i"), Sp, Mapsto, Sp, Call("sensor", F.Id("i"), F.Id("x")), Close);
        Formula family = Seq(F.Id("i"), Sp, Mapsto, Sp,
            Call("ker", Call("sensor", F.Id("i"))));
        return Disp(Seq(
            Forall, Sp, sensor, Colon, Sp,
            Arrow(F.Id("I"), Arrow(F.Id("X"), F.Id("O"))), Comma, Sp,
            Call("ker", joint), Sp, Eq, Sp, Call("iInter", family), Dot));
    }
}
