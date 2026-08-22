using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Restoration;

internal sealed class TargetRecoveryCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A process preserves a target exactly when it creates no target-sensitive fiber defect.",
        H("Target Recovery Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-recovery-factorization-fiber-and-defect-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion."
                        + "target_recovery_criterion"),
                H("Recovery is equivalent to absence of a target defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let U be a process readout and T the target to recover. The inhabited "
                            + "state premise supplies a target value for extending a factor map "
                            + "to process outputs outside the realized range.")),
                    Paragraph(Text(
                        "The defect relation is constructed from U and T. It contains exactly "
                            + "the pairs merged by U but separated by T, so its nonemptiness is "
                            + "the public witness that recovery fails.")),
                    Paragraph(Text(
                        "The accepted answerability criterion supplies all three positive "
                            + "equivalences and directly applies the pinned whole-codomain "
                            + "factorization theorem. Negating its empty-defect equivalence "
                            + "gives the final merged-state characterization."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Factorization(
        Formula processState, Formula targetState, Formula process, Formula target)
    {
        Formula recover = F.Id("r");
        return Seq(
            Exists, Sp, recover, Colon, Sp, Arrow(processState, targetState), Comma, Sp,
            target, Sp, Eq, Sp, recover, Sp, Circ, Sp, process);
    }

    private static Formula FiberConstancy(
        Formula state, Formula process, Formula target)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Apply(process, x), Sp, Eq, Sp, Apply(process, y), Sp, Rightarrow, Sp,
            Apply(target, x), Sp, Eq, Sp, Apply(target, y));
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula processState = F.Id("Y");
        Formula targetState = F.Id("Z");
        Formula process = F.Id("U");
        Formula target = F.Id("T");
        Formula factorization = Factorization(processState, targetState, process, target);
        Formula fiberConstancy = FiberConstancy(state, process, target);
        Formula defect = Call("defectRelation", process, target);
        Formula emptyDefect = Seq(defect, Sp, Eq, Sp, Emptyset);
        Formula nonemptyDefect = Call("Nonempty", defect);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, processState, Comma, Sp, targetState,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Nonempty")),
            Open, state, Close, CloseBracket, Comma, Sp,
            process, Colon, Sp, Arrow(state, processState), Comma, Sp,
            target, Colon, Sp, Arrow(state, targetState), Comma, RowBreak, Grp(),
            Open, factorization, Sp, Leftrightarrow, Sp, fiberConstancy, Close,
            Sp, Land, RowBreak, Grp(),
            Open, fiberConstancy, Sp, Leftrightarrow, Sp, emptyDefect, Close,
            Sp, Land, RowBreak, Grp(),
            Open, emptyDefect, Sp, Leftrightarrow, Sp, factorization, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Neg, Sp, Open, factorization, Close, Sp, Leftrightarrow, Sp,
            nonemptyDefect, Close, Dot));
    }
}
