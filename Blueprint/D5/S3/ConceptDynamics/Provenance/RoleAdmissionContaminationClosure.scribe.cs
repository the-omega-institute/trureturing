using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Provenance;

internal sealed class RoleAdmissionContaminationClosureDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure."
            + "admissible_judge_append_invariant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Snapshot-bounded judge admission is unchanged by ledger events appended after "
            + "the snapshot adjudication point.",
        H("Role Admission and Contamination Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("admissible-judge-append-invariant"),
                DeclarationHandle.Create(Declaration),
                H("Later ledger events cannot flip frozen-round admission"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen commitment carries its own round, freeze point, and "
                            + "adjudication point. Judge admission therefore has no independent "
                            + "caller-supplied cutoff or round.")),
                    Paragraph(Text(
                        "Both recorded roles and adaptive uses inspect only role events whose "
                            + "event number is at most the snapshot adjudication point. The "
                            + "admission predicate also requires a post-freeze first-seen time, "
                            + "exclusion from the reflexive-transitive dependency closure, and "
                            + "absence of adaptive use.")),
                    Paragraph(Text(
                        "If every appended event is strictly later than that adjudication point, "
                            + "none enters either cutoff-filtered ledger query. Admission is "
                            + "therefore identical before and after the append; future Tune and "
                            + "Adjudicate events are explicit instances.")),
                    Paragraph(Text(
                        "The companion formal specification defines contamination as reachability "
                            + "from a record set. Thus derived functions, digests, labels, human "
                            + "selections, and trained intermediates remain source-graph facts; "
                            + "hiding an original identifier does not alter admission."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Comma, Sp]);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula ledger = F.Id("L");
        Formula delta = Delta;
        Formula snapshot = Seq(F.Id("K"), Underscore, Grp(F.Id("n")));
        Formula roleEvent = F.Id("e");
        Formula evidence = F.Id("r");
        Formula eventNumber = Apply(F.Id("eventNumber"), roleEvent);
        Formula cutoff = Apply(F.Id("adjudicationPoint"), snapshot);
        Formula late = Seq(
            Forall, Sp, roleEvent, Comma, Sp,
            Open,
            new Formula.Relation(
                roleEvent, FormulaRelationOperator.MemberOf, delta),
            Sp, Rightarrow, Sp,
            new Formula.Relation(
                cutoff, FormulaRelationOperator.LessThan, eventNumber),
            Close);
        Formula extendedLedger = Seq(ledger, Sp, Plus, Plus, Sp, delta);
        Formula extendedAdmission = Apply(
            F.Id("AdmissibleJudge"), extendedLedger, evidence, snapshot);
        Formula originalAdmission = Apply(
            F.Id("AdmissibleJudge"), ledger, evidence, snapshot);

        return Disp(Seq(
            Forall, Sp, ledger, Comma, Sp, delta, Comma, Sp, snapshot, Comma,
            RowBreak, Grp(),
            Open, late, Close, Sp, Rightarrow, Sp,
            Open, Forall, Sp, evidence, Comma, Sp,
            extendedAdmission, Sp, Iff, Sp, originalAdmission, Close, Dot));
    }
}
