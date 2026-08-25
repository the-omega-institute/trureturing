using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class DomainImmunizationAuditDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Audits/DomainImmunizationAudit."
            + "domain_immunization_audit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target-dependent domain restriction can erase admitted defects while deleting "
            + "empirical states.",
        H("Domain Immunization Audit"),
        Blocks(Describe.Lean(
            DescribeId.Create("domain-immunization-audit"),
            DeclarationHandle.Create(Declaration),
            H("Domain immunization requires deletion and dependence audits"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every defective readout on a finite state carrier, a witnessed target "
                        + "collision selects a singleton admitted domain. The restricted readout "
                        + "has empty target defect, and the displayed complement count records "
                        + "exactly how many states were deleted.")),
                Paragraph(Text(
                    "The Boolean clause is the required contrast model: the constant readout has "
                        + "a full-domain target defect, while the target-defined one-state domain "
                        + "has none. Both retained and deleted counts are explicit.")),
                Paragraph(Text(
                    "For a cumulative family of counterexamples, the admitted domains are their "
                        + "complements. They remain disjoint from all current counterexamples, are "
                        + "antitone, and shrink strictly whenever the counterexample set grows "
                        + "strictly."))),
            DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);

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
        Formula admitted = F.Id("A");
        Formula defect = Call("Defect", readout, target);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula empty = Emptyset;
        Formula one = D(1);

        Formula universalClause = Seq(
            Forall, Sp, stateType, Comma, Sp, coordinateType, Comma, Sp, targetType,
            Colon, Sp, type, Comma, Sp, Typeclass("Finite", stateType), Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, Arrow(stateType, coordinateType), Comma, Sp,
            target, Colon, Sp, Arrow(stateType, targetType), Comma,
            RowBreak, Grp(),
            Call("Nonempty", defect), Sp, Rightarrow, Sp,
            Exists, Sp, counterexample, Colon, Sp,
            stateType, Sp, Times, Sp, stateType, Comma, Sp,
            Exists, Sp, admitted, Colon, Sp, Call("Set", stateType), Comma,
            RowBreak, Grp(),
            counterexample, Sp, InMacro, Sp, defect, Sp, Land, Sp,
            admitted, Sp, Eq, Sp, Call("singleton", Call("fst", counterexample)),
            Sp, Land,
            RowBreak, Grp(),
            RestrictedDefect(readout, target, admitted), Sp, Eq, Sp, empty,
            Sp, Land, Sp,
            Call("ncard", admitted), Sp, Eq, Sp, one, Sp, Land,
            RowBreak, Grp(),
            Call("ncard", Call("compl", admitted)), Sp, Eq, Sp,
            Call("NatCard", stateType), Sp, Minus, Sp, one);

        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula booleanReadout = F.Id("Czero");
        Formula booleanTarget = F.Id("Tzero");
        Formula booleanAdmitted = F.Id("Azero");
        Formula point = F.Id("x");
        Formula falseValue = F.Id("false");
        Formula booleanDefect = Call("Defect", booleanReadout, booleanTarget);
        Formula targetDomain = Seq(
            OpenBrace, point, Sp, Mid, Sp,
            Apply(booleanTarget, point), Sp, Eq, Sp, falseValue, CloseBrace);
        Formula booleanClause = Seq(
            booleanReadout, Sp, Eq, Sp, Call("constant", F.Id("unit")), Comma, Sp,
            booleanTarget, Sp, Eq, Sp, F.Id("id"), Comma, Sp,
            booleanAdmitted, Sp, Eq, Sp, targetDomain, Colon,
            RowBreak, Grp(),
            Call("Nonempty", booleanDefect), Sp, Land, Sp,
            RestrictedDefect(booleanReadout, booleanTarget, booleanAdmitted),
            Sp, Eq, Sp, empty, Sp, Land,
            RowBreak, Grp(),
            Call("ncard", booleanAdmitted), Sp, Eq, Sp, one, Sp, Land, Sp,
            Call("ncard", Call("compl", booleanAdmitted)), Sp, Eq, Sp, one,
            Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, point, Colon, Sp, boolean, Comma, Sp,
            point, Sp, InMacro, Sp, booleanAdmitted, Sp, Iff, Sp,
            Apply(booleanTarget, point), Sp, Eq, Sp, falseValue);

        Formula sequenceState = F.Id("S");
        Formula counterexamples = F.Id("E");
        Formula admissions = F.Id("M");
        Formula stage = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula currentCounterexamples = Apply(counterexamples, stage);
        Formula nextStage = Seq(stage, Sp, Plus, Sp, one);
        Formula nextCounterexamples = Apply(counterexamples, nextStage);
        Formula currentAdmissions = Apply(admissions, stage);
        Formula nextAdmissions = Apply(admissions, nextStage);
        Formula sequenceClause = Seq(
            Forall, Sp, sequenceState, Colon, Sp, type, Comma, Sp,
            counterexamples, Colon, Sp, naturals, Sp, To, Sp,
            Call("Set", sequenceState), Comma,
            RowBreak, Grp(),
            Call("Monotone", counterexamples), Sp, Rightarrow, Sp,
            Exists, Sp, admissions, Colon, Sp, naturals, Sp, To, Sp,
            Call("Set", sequenceState), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, stage, Comma, Sp,
            currentAdmissions, Sp, Eq, Sp, Call("compl", currentCounterexamples),
            Close, Sp, Land, Sp, Call("Antitone", admissions), Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, stage, Comma, Sp,
            Call("inter", currentAdmissions, currentCounterexamples),
            Sp, Eq, Sp, empty, Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, stage, Comma, Sp,
            currentCounterexamples, Sp, Subset, Sp, nextCounterexamples,
            Sp, Rightarrow, Sp,
            nextAdmissions, Sp, Subset, Sp, currentAdmissions, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, universalClause, Close, Sp, Land,
            RowBreak, Grp(),
            Open, booleanClause, Close, Sp, Land,
            RowBreak, Grp(),
            Open, sequenceClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

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
}
