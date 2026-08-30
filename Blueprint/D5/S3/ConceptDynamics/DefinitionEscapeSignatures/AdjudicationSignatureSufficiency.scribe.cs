using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeSignatures;

internal sealed class AdjudicationSignatureSufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeSignatures/"
            + "AdjudicationSignatureSufficiency.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-coordinate adjudication signature preserves non-anticipation, admissible "
            + "judging, and scientific gain, but not target laundering's whole-commitment "
            + "report identity.",
        H("Adjudication-Signature Sufficiency and Its Target-Laundering Failure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("non-anticipating-signature-sufficiency"),
                DeclarationHandle.Create(
                    Prefix + "non_anticipating_signature_sufficiency"),
                H("OP1-NA: equal signatures preserve non-anticipation"),
                StatementSource.FromAuthor(NonAnticipatingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a common record in the finite history, equality of the decision-visible, "
                        + "freeze-visible, and directly contaminated coordinates transports each "
                        + "conjunct of NonAnticipating in both directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-judge-signature-sufficiency"),
                DeclarationHandle.Create(
                    Prefix + "admissible_judge_signature_sufficiency"),
                H("OP1-AJ: equal signatures preserve admissible judging"),
                StatementSource.FromAuthor(AdmissibleJudgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fourth coordinate records existence of adjudicate events and of each "
                        + "generate, tune, or select event together with its dependency-closure "
                        + "touch bit. It therefore transports both the positive role requirement "
                        + "and the negated adaptive-contamination requirement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scientific-gain-signature-sufficiency"),
                DeclarationHandle.Create(
                    Prefix + "scientific_gain_signature_sufficiency"),
                H("OP1-SG: equal signatures preserve scientific gain"),
                StatementSource.FromAuthor(ScientificGainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "SameOutSG fixes the committed and baseline action sets and the comparator. "
                        + "The only remaining history-dependent conjunct is NonAnticipating, "
                        + "which is supplied by OP1-NA."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-laundering-signature-counterexample"),
                DeclarationHandle.Create(
                    Prefix + "target_laundering_signature_counterexample"),
                H("OP1-TL: equal signatures do not preserve target laundering"),
                StatementSource.FromAuthor(TargetLaunderingCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite witness uses Boolean event, evidence, artifact, and time "
                            + "types with empty valid role ledgers. The two new commitments differ "
                            + "only in adjudication.frozenAt; all four signature coordinates and "
                            + "all commitment fields outside adjudication are equal.")),
                    Paragraph(Text(
                        "The common report names the first new commitment as its revised object. "
                            + "SketchTargetLaundering is true on that side, but the same report "
                            + "cannot also name the second, unequal commitment. The omitted "
                            + "frozenAt field separately changes the timestamp identity as well.")),
                    Paragraph(Text(
                        "SketchTargetLaundering is the frozen Lean name for the no-arrival "
                            + "target-laundering interface used by Part 55; the distinct prose-level "
                            + "TargetLaundering declaration has an additional arrival argument."))),
                DescribeRole.Theorem))));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula NotFormula(Formula value) => new Formula.Not(value);

    private static Formula Signature(
        Formula records, Formula ledger, Formula snapshot, Formula valid) =>
        Call("adjudicationSignature", records, ledger, snapshot, valid);

    private static Formula NonAnticipatingFormula()
    {
        Formula records = F.Id("Z"), record = F.Id("z");
        Formula leftLedger = F.Id("L"), rightLedger = F.Id("R");
        Formula left = F.Id("K"), right = F.Id("J");
        Formula leftValid = F.Id("v"), rightValid = F.Id("w");
        Formula premise = And(
            Equal(
                Signature(records, leftLedger, left, leftValid),
                Signature(records, rightLedger, right, rightValid)),
            Call("SameOutNA", records, record));
        Formula conclusion = IffFormula(
            Call("NonAnticipating", left, record),
            Call("NonAnticipating", right, record));
        return F.Disp(Implies(premise, conclusion));
    }

    private static Formula AdmissibleJudgeFormula()
    {
        Formula records = F.Id("Z"), record = F.Id("r");
        Formula leftLedger = F.Id("L"), rightLedger = F.Id("R");
        Formula left = F.Id("K"), right = F.Id("J");
        Formula leftValid = F.Id("v"), rightValid = F.Id("w");
        Formula premise = And(
            Equal(
                Signature(records, leftLedger, left, leftValid),
                Signature(records, rightLedger, right, rightValid)),
            Call("SameOutAJ", records, record));
        Formula conclusion = IffFormula(
            Call("AdmissibleJudge", leftLedger, left, leftValid, record),
            Call("AdmissibleJudge", rightLedger, right, rightValid, record));
        return F.Disp(Implies(premise, conclusion));
    }

    private static Formula ScientificGainFormula()
    {
        Formula records = F.Id("Z"), record = F.Id("z");
        Formula leftLedger = F.Id("L"), rightLedger = F.Id("R");
        Formula left = F.Id("K"), right = F.Id("J");
        Formula leftValid = F.Id("v"), rightValid = F.Id("w");
        Formula evaluate = F.Id("E"), committed = F.Id("a"), baseline = F.Id("b");
        Formula premise = And(
            Equal(
                Signature(
                    records, leftLedger, Call("adjudication", left), leftValid),
                Signature(
                    records, rightLedger, Call("adjudication", right), rightValid)),
            Call("SameOutSG", records, record, left, right));
        Formula conclusion = IffFormula(
            Call("ScientificGain", evaluate, left, record, committed, baseline),
            Call("ScientificGain", evaluate, right, record, committed, baseline));
        return F.Disp(Implies(premise, conclusion));
    }

    private static Formula TargetLaunderingCounterexampleFormula()
    {
        Formula records = F.Id("Z"), record = F.Id("true");
        Formula oldLeft = F.Id("K"), newLeft = F.Id("N");
        Formula oldRight = F.Id("J"), newRight = F.Id("M");
        Formula oldLeftLedger = F.Id("L"), newLeftLedger = F.Id("R");
        Formula oldRightLedger = F.Id("P"), newRightLedger = F.Id("Q");
        Formula oldLeftValid = F.Id("v"), newLeftValid = F.Id("w");
        Formula oldRightValid = F.Id("x"), newRightValid = F.Id("y");
        Formula evaluate = F.Id("E"), report = F.Id("T");
        Formula boolean = Call("Bool"), unit = Call("Unit");
        Formula commitment = Call("Commitment"), ledger = Call("Ledger");
        Formula equalOldSignature = Equal(
            Signature(
                records, oldLeftLedger, Call("adjudication", oldLeft), oldLeftValid),
            Signature(
                records, oldRightLedger, Call("adjudication", oldRight), oldRightValid));
        Formula equalNewSignature = Equal(
            Signature(
                records, newLeftLedger, Call("adjudication", newLeft), newLeftValid),
            Signature(
                records, newRightLedger, Call("adjudication", newRight), newRightValid));
        Formula sameOut = Call(
            "SameOutTL", records, record, oldLeft, newLeft, oldRight, newRight);
        Formula leftLaundering = Call(
            "SketchTargetLaundering", evaluate, oldLeft, newLeft, record, report);
        Formula rightLaundering = Call(
            "SketchTargetLaundering", evaluate, oldRight, newRight, record, report);
        Formula body = And(
            equalOldSignature,
            And(
                equalNewSignature,
                And(sameOut, And(leftLaundering, NotFormula(rightLaundering)))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("Z", Call("Finset", boolean)),
                Bound("K", commitment),
                Bound("N", commitment),
                Bound("J", commitment),
                Bound("M", commitment),
                Bound("L", ledger),
                Bound("R", ledger),
                Bound("P", ledger),
                Bound("Q", ledger),
                Bound("v", Call("ValidTrace", oldLeftLedger,
                    Call("adjudication", oldLeft))),
                Bound("w", Call("ValidTrace", newLeftLedger,
                    Call("adjudication", newLeft))),
                Bound("x", Call("ValidTrace", oldRightLedger,
                    Call("adjudication", oldRight))),
                Bound("y", Call("ValidTrace", newRightLedger,
                    Call("adjudication", newRight))),
                Bound("E", new Formula.TypeArrow(
                    commitment, new Formula.TypeArrow(boolean, unit))),
                Bound("T", Call("RegradeReport",
                    commitment, boolean, unit, boolean, evaluate)),
            ],
            body));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
