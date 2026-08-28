using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class RetrospectiveLookupFailureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite table copying has zero retrospective loss but fails non-anticipation.",
        H("Retrospective Lookup Failure"),
        Blocks(Describe.Lean(
            DescribeId.Create("lookup-copy-zero-loss-and-nonanticipating-failure"),
            DeclarationHandle.Create(Prefix + "lookup_copy_zero_loss_and_nonanticipating_failure"),
            H("Lookup copying is exact retrospectively but contaminated for anticipation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary finite record type, CopyComparison supplies the observed "
                        + "answer, a Nat-valued pointwise loss, and the self-loss-zero law. "
                        + "The tableCopy is exactly the observed-answer function, and "
                        + "retrospectiveLoss is only the finite sum of those pointwise losses, "
                        + "with no complexity or regularization term.")),
                Paragraph(Text(
                    "The self-loss law makes every summand zero, so the lookup copier's total "
                        + "retrospective loss is zero. IncorporatesTableCopy places every record "
                        + "in the commitment's evidence dependency closure; this contradicts the "
                        + "absence-of-dependency clause of NonAnticipating for every record, even "
                        + "when the record was frozen beforehand.")),
                Paragraph(Text(
                    "PositiveProspectiveGain is an independent future-evaluation quantity. The "
                        + "zero prospective-gain function witnesses that zero retrospective loss "
                        + "does not entail a strictly positive prospective gain. Concrete Bool/Nat "
                        + "examples separately show exact lookup loss zero and a one-unit loss for "
                        + "a constant wrong copy."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Not(Formula formula) => new Formula.Not(formula);

    private static Formula TypeUniverse() => F.Id("Type");

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Instance(string name, Formula carrier) =>
        Seq(OpenBracket, Call(name, carrier), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula record = F.Id("Z");
        Formula answer = F.Id("Answer");
        Formula comparison = F.Id("comparison");
        Formula commitment = F.Id("commitment");
        Formula copier = Call("tableCopy", comparison);
        Formula loss = Call("retrospectiveLoss", comparison, copier);
        Formula zeroLoss = Equal(loss, D(0));
        Formula recordVariable = F.Id("z");
        Formula recordLoss = Seq(
            Open, Forall, Sp, recordVariable, Colon, Sp, record, Comma, Sp,
            Not(Call("NonAnticipating", commitment, recordVariable)), Close);
        Formula gain = F.Id("prospectiveGain");
        Formula gainType = Arrow(
            Seq(Open, record, Sp, To, Sp, answer, Close),
            NaturalNumbers());
        Formula allGains = Seq(
            Forall, Sp, gain, Colon, Sp, gainType, Comma, Sp,
            Call("PositiveProspectiveGain", gain, copier));
        Formula noPositiveGain = Not(Implies(zeroLoss, allGains));
        Formula conclusion = And(zeroLoss, And(recordLoss, noPositiveGain));
        Formula instances = And(
            Instance("Fintype", record),
            Instance("DecidableEq", record));
        Formula premises = Implies(
            And(instances, Call("IncorporatesTableCopy", commitment)), conclusion);

        return Disp(Seq(
            Forall, Sp, record, Comma, Sp, answer, Colon, Sp, TypeUniverse(), Comma, Sp,
            comparison, Colon, Sp, Call("CopyComparison", record, answer), Comma, Sp,
            commitment, Colon, Sp, Call("CopyCommitment", record), Comma, Sp,
            premises, Dot));
    }
}
