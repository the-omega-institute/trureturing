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
            + "the snapshot adjudication point, when both traces are valid.",
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
                        "The frozen commitment carries its own round, freeze event, decision "
                            + "event, filtration, dependency closure, and evidence-dependency "
                            + "set. Judge admission therefore has no independent caller-supplied "
                            + "cutoff or round.")),
                    Paragraph(Text(
                        "Both recorded roles and adaptive uses inspect only events in the "
                            + "validated event, round, and time prefix. The admission predicate "
                            + "requires adjudication role presence, absence at freeze, absence "
                            + "from the snapshot dependency set, and absence of adaptive use.")),
                    Paragraph(Text(
                        "If every appended event is strictly later than the decision event, none "
                            + "enters the event prefix. With ValidTrace proofs on both ledgers, "
                            + "admission is therefore identical before and after the append.")),
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
        Formula extendedLedger = F.Id("Lprime");
        Formula snapshot = Seq(F.Id("K"), Underscore, Grp(F.Id("n")));
        Formula validLedger = F.Id("v");
        Formula validExtended = F.Id("vprime");
        Formula extension = F.Id("h");
        Formula evidence = F.Id("r");
        Formula extendedAdmission = Apply(
            F.Id("AdmissibleJudge"), extendedLedger, snapshot, validExtended, evidence);
        Formula originalAdmission = Apply(
            F.Id("AdmissibleJudge"), ledger, snapshot, validLedger, evidence);
        Formula premise = Apply(
            F.Id("AppendOnlyExtension"), ledger, extendedLedger, snapshot, extension);
        Formula oldTrace = Apply(
            F.Id("ValidTrace"), ledger, snapshot, validLedger);
        Formula extendedTrace = Apply(
            F.Id("ValidTrace"), extendedLedger, snapshot, validExtended);
        Formula allPremises = Seq(
            Open, oldTrace, Sp, Land, Sp, extendedTrace, Sp, Land, Sp,
            premise, Close);

        return Disp(Seq(
            Forall, Sp, ledger, Comma, Sp, extendedLedger, Comma, Sp, snapshot,
            Comma, Sp, validLedger, Comma, Sp, validExtended, Comma, Sp, extension,
            Comma, Sp, evidence,
            RowBreak, Grp(),
            allPremises, Sp, Rightarrow, Sp,
            Open, extendedAdmission, Sp, Iff, Sp, originalAdmission, Close, Dot));
    }
}
