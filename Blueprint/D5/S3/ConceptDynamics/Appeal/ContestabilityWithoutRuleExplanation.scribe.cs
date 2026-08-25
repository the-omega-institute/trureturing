using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Appeal;

internal sealed class ContestabilityWithoutRuleExplanationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Appeal/ContestabilityWithoutRuleExplanation."
            + "contestable_outcome_can_lack_rule_explanation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact appeal evidence can make outcomes contestable while the rule remains absent from "
            + "the explanation log.",
        H("Contestability Without Rule Explanation"),
        Blocks(Describe.Lean(
            DescribeId.Create("contestable-outcome-can-lack-rule-explanation"),
            DeclarationHandle.Create(Declaration),
            H("A contestable outcome need not reveal its governing rule"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every Boolean target on a two-coordinate state space, the appeal readout "
                        + "is chosen to equal that target. The joined case-and-appeal interface "
                        + "therefore determines the canonical effective target readout.")),
                Paragraph(Text(
                    "Independently, the governing rule reads the second state coordinate while the "
                        + "explanation log is constant. Two states with different rule values have "
                        + "the same log value, so the rule cannot factor through that log.")),
                Paragraph(Text(
                    "The public theorem states appeal equality, target contestability, and failed "
                        + "rule explanation as separate clauses on the source readouts."))),
            DescribeRole.Theorem))));

    private static Formula Concept(Formula state, Formula value) =>
        Call("Concept", state, value);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula state = Seq(boolean, Sp, Times, Sp, boolean);
        Formula target = F.Id("T");
        Formula rule = F.Id("R");
        Formula log = F.Id("L");
        Formula caseReadout = F.Id("C");
        Formula appeal = F.Id("A");
        Formula booleanReadout = Concept(state, boolean);
        Formula unitReadout = Concept(state, unit);
        Formula appealEqualsTarget = Seq(appeal, Sp, Eq, Sp, target);
        Formula targetContestable = Call(
            "Refines",
            Call("canonicalTargetReadout", target),
            Call("conceptJoin", caseReadout, appeal));
        Formula ruleNotExplained = new Formula.Not(Call("Refines", rule, log));
        Formula clauses = And(
            appealEqualsTarget,
            And(targetContestable, ruleNotExplained));
        Formula countermodel = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(FormulaIdentifier.Create("R"), booleanReadout),
                new(FormulaIdentifier.Create("L"), unitReadout),
                new(FormulaIdentifier.Create("C"), unitReadout),
                new(FormulaIdentifier.Create("A"), booleanReadout),
            ],
            clauses);

        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("T"),
            booleanReadout,
            countermodel));
    }
}
