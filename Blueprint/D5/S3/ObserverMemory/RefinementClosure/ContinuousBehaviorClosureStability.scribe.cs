using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class ContinuousBehaviorClosureStabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous dynamics preserve the closure of realizable behaviors.",
        H("Continuous Behavior Closure Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-behavior-closure-stability"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/RefinementClosure/"
                        + "ContinuousBehaviorClosureStability."
                        + "continuous_dynamics_preserves_behavior_closure"),
                H("Continuous actions preserve behavior closure"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B carry a topology, let I be its set of realizable behaviors, "
                            + "and let S be a continuous self-action on B.")),
                    Paragraph(Text(
                        "When S maps every realizable behavior back into I, continuity sends "
                            + "every limit of realizable behaviors into the closure of I.")),
                    Paragraph(Text(
                        "The proof applies the pinned closure mapping theorem directly; no "
                            + "parallel closure or dynamics primitive is introduced."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula behavior = F.Id("B");
        Formula action = F.Id("S");
        Formula realizable = F.Id("I");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula setBehavior = Call("Set", behavior);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(behavior, type), Comma, Sp,
                Call("TopologicalSpace", behavior), Comma),
            Seq(
                Typed(action, Arrow(behavior, behavior)), Comma, Sp,
                Typed(realizable, setBehavior), Comma),
            Seq(
                Call("Continuous", action), Sp, Land, Sp,
                Call("MapsTo", action, realizable, realizable), Sp, Rightarrow),
            Seq(
                Call("MapsTo", action, Call("closure", realizable),
                    Call("closure", realizable)), Dot),
        ]));
    }
}
