using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class CongruenceKernelSensorFusionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Refinement/CongruenceKernelSensorFusion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward-congruence completion commutes with arbitrary sensor intersections.",
        H("Congruence Kernel Sensor Fusion"),
        Blocks(Describe.Lean(
            DescribeId.Create("congruence-kernel-commutes-with-sensor-intersections"),
            DeclarationHandle.Create(Prefix + "congruence_kernel_iInter"),
            H("Congruence kernel commutes with sensor intersections"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a state endomorphism and an arbitrary indexed family of state "
                        + "relations.")),
                Paragraph(Text(
                    "Membership in the congruence kernel of the intersection means that every "
                        + "iterate lies in every sensor relation.")),
                Paragraph(Text(
                    "Exchanging the universal quantifiers over iterates and sensor indices gives "
                        + "the intersection of the individual congruence kernels. No finiteness "
                        + "of the sensor index is required."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula tau = F.Id("tau");
        Formula relations = F.Id("R");
        Formula familyIntersection = Call("iInter", Seq(
            F.Id("i"), Sp, Mapsto, Sp, Call("R", F.Id("i"))));
        Formula completedFamily = Call("iInter", Seq(
            F.Id("i"), Sp, Mapsto, Sp,
            Call("congruenceKernel", tau, Call("R", F.Id("i")))));
        return Disp(Seq(
            Forall, Sp, tau, Colon, Sp, Arrow(F.Id("Y"), F.Id("Y")), Comma, Sp,
            relations, Colon, Sp,
            Arrow(F.Id("I"), Call("StateRelation", F.Id("Y"))), Comma,
            RowBreak, Grp(),
            Call("congruenceKernel", tau, familyIntersection), Sp, Eq, Sp,
            completedFamily, Dot));
    }
}
