using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class CongruenceKernelSensorFusionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Refinement/CongruenceKernelSensorFusion."
            + "congruence_kernel_iInter";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward-congruence completion commutes with arbitrary sensor intersections.",
        H("Congruence-Kernel Sensor Fusion"),
        Blocks(Describe.Lean(
            DescribeId.Create("completion-commutes-with-sensor-intersection"),
            DeclarationHandle.Create(Declaration),
            H("Completion commutes with sensor intersection"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each relation records the pairs left indistinguishable by one sensor. "
                        + "Their intersection is the joint sensor kernel.")),
                Paragraph(Text(
                    "Membership in the completed joint kernel quantifies first over update "
                        + "iterations and then over sensors. Membership in the intersection "
                        + "of completed kernels quantifies in the reverse order. Exchanging "
                        + "these two universal quantifiers proves equality.")),
                Paragraph(Text(
                    "The index type may be infinite or empty. No finiteness, decidability, "
                        + "topology, or invertibility hypothesis is added."))),
            DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula state = F.Id("Y");
        Formula update = F.Id("tau");
        Formula relations = F.Id("R");
        Formula relationType = Call("StateRelation", state);
        Formula intersection = Call("iInter", relations);
        Formula completedIntersection =
            Call("congruenceKernel", update, intersection);
        Formula intersectionOfCompletions = Call(
            "iInter", Call("completedFamily", update, relations));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(indexType, Comma, Sp, state), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(update, Seq(state, Sp, To, Sp, state)),
            Comma, RowBreak, Grp(),
            Typed(relations, Seq(indexType, Sp, To, Sp, relationType)),
            Comma, RowBreak, Grp(),
            completedIntersection, Sp, Eq, Sp, intersectionOfCompletions, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
