using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class TargetConditionedAdmissionAuditDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Audits/TargetConditionedAdmissionAudit."
            + "target_conditioned_admission_audit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target-conditioned admission can erase defects only by deleting states.",
        H("Target-Conditioned Admission Audit"),
        Blocks(Describe.Lean(
            DescribeId.Create("target-conditioned-admission-audit"),
            DeclarationHandle.Create(Declaration),
            H("Restricted closure records deletion and target dependence"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A target collision supplies two distinct states. Restricting both channels "
                        + "to the singleton containing the first state removes all target defects, "
                        + "but the complement has positive cardinality.")),
                Paragraph(Text(
                    "In the Boolean contrast, the readout stays constant. Its whole-domain defect "
                        + "is nonempty, its target-conditioned singleton domain has no defect, and "
                        + "changing the target from identity to negation changes the admitted set.")),
                Paragraph(Text(
                    "The final clause takes admission domains as independent inputs. When an "
                        + "admitted counterexample is removed at each update, that state is absent "
                        + "at the next stage and the domain shrinks strictly."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula RestrictedDefect(
        Formula readout, Formula target, Formula admitted) =>
        Call("Defect", Call("restrict", readout, admitted),
            Call("restrict", target, admitted));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula readout = F.Id("C");
        Formula target = F.Id("T");
        Formula counterexample = F.Id("z");
        Formula singleton = Call("singleton", Call("fst", counterexample));
        Formula complement = Call("compl", singleton);
        Formula defect = Call("Defect", readout, target);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula empty = Emptyset;
        Formula zero = D(0);
        Formula one = D(1);

        Formula witnessedRestriction = Seq(
            Forall, Sp, stateType, Comma, Sp, coordinateType, Comma, Sp,
            targetType, Colon, Sp, type, Comma, Sp,
            Seq(OpenBracket, Call("Finite", stateType), CloseBracket), Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, Arrow(stateType, coordinateType), Comma, Sp,
            target, Colon, Sp, Arrow(stateType, targetType), Comma,
            RowBreak, Grp(),
            Call("Nonempty", defect), Sp, Rightarrow, Sp,
            Exists, Sp, counterexample, Colon, Sp,
            stateType, Sp, Times, Sp, stateType, Comma,
            RowBreak, Grp(),
            counterexample, Sp, InMacro, Sp, defect, Sp, Land, Sp,
            RestrictedDefect(readout, target, singleton), Sp, Eq, Sp, empty,
            Sp, Land, Sp,
            zero, Sp, Lt, Sp, Call("ncard", complement));

        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula booleanReadout = new Formula.Subscript(F.Id("C"), zero);
        Formula identity = F.Id("id");
        Formula negation = F.Id("not");
        Formula rule = F.Id("A");
        Formula booleanTarget = F.Id("U");
        Formula point = F.Id("x");
        Formula ruleAtIdentity = Apply(rule, identity);
        Formula targetDomain = Seq(
            OpenBrace, point, Sp, Mid, Sp,
            Apply(booleanTarget, point), Sp, Eq, Sp, F.Id("false"), CloseBrace);
        Formula booleanClause = Seq(
            booleanReadout, Colon, Sp, Arrow(boolean, unit), Sp, Eq, Sp,
            Call("constant", F.Id("unit")), Comma,
            RowBreak, Grp(),
            rule, Colon, Sp,
            Arrow(Seq(Open, Arrow(boolean, boolean), Close), Call("Set", boolean)),
            Comma, Sp, Apply(rule, booleanTarget), Sp, Eq, Sp, targetDomain,
            Colon,
            RowBreak, Grp(),
            Call("Nonempty", Call("Defect", booleanReadout, identity)),
            Sp, Land, Sp,
            RestrictedDefect(booleanReadout, identity, ruleAtIdentity),
            Sp, Eq, Sp, empty, Sp, Land,
            RowBreak, Grp(),
            Apply(rule, identity), Sp, Neq, Sp, Apply(rule, negation),
            Sp, Land, Sp,
            Call("ncard", Call("compl", ruleAtIdentity)), Sp, Eq, Sp, one);

        Formula updateState = F.Id("S");
        Formula admissions = F.Id("M");
        Formula counterexamples = F.Id("e");
        Formula stage = F.Id("n");
        Formula nextStage = Seq(stage, Sp, Plus, Sp, one);
        Formula currentAdmission = Apply(admissions, stage);
        Formula nextAdmission = Apply(admissions, nextStage);
        Formula currentCounterexample = Apply(counterexamples, stage);
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula updateClause = Seq(
            Forall, Sp, updateState, Colon, Sp, type, Comma, Sp,
            admissions, Colon, Sp, Arrow(naturals, Call("Set", updateState)),
            Comma, Sp,
            counterexamples, Colon, Sp, Arrow(naturals, updateState), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, stage, Comma, Sp,
            currentCounterexample, Sp, InMacro, Sp, currentAdmission, Close,
            Sp, Rightarrow,
            RowBreak, Grp(),
            Open, Forall, Sp, stage, Comma, Sp,
            nextAdmission, Sp, Eq, Sp,
            Call("diff", currentAdmission, Call("singleton", currentCounterexample)),
            Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, stage, Comma, Sp,
            Neg, Sp, Open, currentCounterexample, Sp, InMacro, Sp, nextAdmission, Close,
            Sp, Land, Sp,
            nextAdmission, Sp, Subset, Sp, currentAdmission);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, witnessedRestriction, Close, Sp, Land,
            RowBreak, Grp(),
            Open, booleanClause, Close, Sp, Land,
            RowBreak, Grp(),
            Open, updateClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
