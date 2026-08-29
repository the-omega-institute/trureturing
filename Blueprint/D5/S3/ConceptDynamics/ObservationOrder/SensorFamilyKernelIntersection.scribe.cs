using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class SensorFamilyKernelIntersectionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ObservationOrder/SensorFamilyKernelIntersection."
            + "joint_readout_kernel_eq_iInter";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A joint sensor kernel is the intersection of all coordinate kernels.",
        H("Sensor Family Kernel Intersection"),
        Blocks(Describe.Lean(
            DescribeId.Create("joint-sensor-kernel-is-the-coordinate-intersection"),
            DeclarationHandle.Create(Declaration),
            H("A joint sensor kernel is the coordinate intersection"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The joint readout sends each source state to its complete function of "
                        + "sensor coordinates.")),
                Paragraph(Text(
                    "Equality of the resulting functions is equivalent to equality at every "
                        + "coordinate. This exchanges function extensionality with membership "
                        + "in the intersection of coordinate kernels.")),
                Paragraph(Text(
                    "The result includes finite, infinite, singleton, and empty sensor "
                        + "families without separate cases."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula source = F.Id("X");
        Formula output = F.Id("O");
        Formula sensor = F.Id("q");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(indexType, Comma, Sp, source, Comma, Sp, output),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(sensor, Seq(indexType, Sp, To, Sp, source, Sp, To, Sp, output)),
            Comma, RowBreak, Grp(),
            Call("K", Call("jointReadout", sensor)), Sp, Eq, Sp,
            Call("iInter", Call("kernelFamily", sensor)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
