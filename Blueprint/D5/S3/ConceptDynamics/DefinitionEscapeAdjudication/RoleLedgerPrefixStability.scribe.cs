using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class RoleLedgerPrefixStabilityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RoleLedgerPrefixStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A valid role ledger rejects events unseen at their own index, and events appended "
            + "strictly after a frozen decision cannot alter its adjudication prefix.",
        H("Role-Ledger Prefix Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invalid-trace-of-unseen-recorded-event"),
                DeclarationHandle.Create(Prefix + "invalid_trace_of_unseen_recorded_event"),
                H("An unseen recorded event invalidates the whole trace"),
                StatementSource.FromAuthor(InvalidTraceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "ValidRoleTrace universally binds every recorded event to the evidence "
                        + "visible at that event's own identifier. A recorded counterexample "
                        + "therefore negates the whole trace; no consumer can recover validity "
                        + "by silently dropping that event."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("append-only-adjudication-role-prefix-unchanged"),
                DeclarationHandle.Create(
                    Prefix + "append_only_adjudication_role_prefix_unchanged"),
                H("A post-decision append preserves the frozen three-coordinate prefix"),
                StatementSource.FromAuthor(PrefixStabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The full RoleUseEvent stores a unique event identifier, evidence, "
                            + "round, role, dependencies, protocol, and physical time. The ledger "
                            + "requires unique strictly ordered identifiers and monotone round and "
                            + "time coordinates. RolesAtInPrefix remains a relational set, so "
                            + "separate uses of the same record are not collapsed.")),
                    Paragraph(Text(
                        "AdjudicationRolePrefix simultaneously restricts event identifier, "
                            + "round, and time. AppendOnlyRoleExtension exposes a literal list "
                            + "tail "
                            + "and proves every tail identifier is strictly greater than the old "
                            + "decision identifier.")),
                    Paragraph(Text(
                        "List membership in the extended ledger splits between the old list and "
                            + "the tail. The tail case contradicts the prefix's at-or-before "
                            + "decision bound, while old events embed into the append. This proves "
                            + "set equality of the full frozen prefix under valid old and new "
                            + "trace hypotheses.")),
                    Paragraph(Text(
                        "This discharges the reject-on-mismatch and append-only prefix-stability "
                            + "claims of definition-escape-completion-theory Part 48.2, atom "
                            + "generic-residual-ae65843df6a0e51d2e107e681bbcbfa35cd1bb922d011d85e"
                            + "ce1c3f466fa444e. "
                            + "The source's semantic gloss for the five role names is represented "
                            + "by the constructors; no statistical independence or generalization "
                            + "claim is added."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Not(Formula value) => new Formula.Not(value);

    private static Formula InvalidTraceFormula()
    {
        Formula ledger = F.Id("L");
        Formula filtration = F.Id("F");
        Formula eventValue = F.Id("e");
        Formula recorded = Member(eventValue, Call("events", ledger));
        Formula unseen = Not(Member(
            Call("evidence", eventValue),
            Call("seen", filtration, Call("eventId", eventValue))));

        return Disp(Implies(
            And(recorded, unseen),
            Not(Call("ValidRoleTrace", ledger, filtration))));
    }

    private static Formula PrefixStabilityFormula()
    {
        Formula filtration = F.Id("F");
        Formula oldLedger = F.Id("L");
        Formula newLedger = F.Id("LNew");
        Formula decision = F.Id("d");
        Formula round = F.Id("n");
        Formula time = Tau;
        Formula hypotheses = And(
            Call("ValidRoleTrace", oldLedger, filtration),
            And(
                Call("ValidRoleTrace", newLedger, filtration),
                Call("AppendOnlyRoleExtension", oldLedger, newLedger, decision)));
        Formula conclusion = Equal(
            Call("AdjudicationRolePrefix", newLedger, decision, round, time),
            Call("AdjudicationRolePrefix", oldLedger, decision, round, time));

        return Disp(Seq(
            Forall, Sp, filtration, Comma, Sp, oldLedger, Comma, Sp, newLedger,
            Comma, Sp, decision, Comma, Sp, round, Comma, Sp, time, Comma, Sp,
            Implies(hypotheses, conclusion), Dot));
    }
}
