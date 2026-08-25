using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Appeal;

internal sealed class RuleCoupledAppealContrastDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Appeal/RuleCoupledAppealContrast."
            + "rule_coupled_appeal_can_repair_without_log_explanation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An appeal computed from the case and hidden rule can recover the target even when "
            + "the explanation log cannot recover that rule.",
        H("Rule-Coupled Appeal Contrast"),
        Blocks(Describe.Lean(
            DescribeId.Create("rule-coupled-appeal-repairs-without-log-explanation"),
            DeclarationHandle.Create(Declaration),
            H("Contestability need not provide rule explanation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The appeal oracle reads the joined rule and case coordinates, while the "
                        + "target oracle reads the same coordinates in the opposite order. The "
                        + "Boolean construction depends on both coordinates and proves the two "
                        + "resulting readouts equal.")),
                Paragraph(Text(
                    "Joining the case readout with that constructed appeal recovers the canonical "
                        + "target readout. The same nonconstant rule used by both constructions "
                        + "still cannot factor through the constant explanation log.")),
                Paragraph(Text(
                    "The appeal-target equality, target recovery, and missing explanation are "
                        + "therefore three public clauses of one shared countermodel."))),
            DescribeRole.Theorem))));

    private static Formula Concept(Formula state, Formula value) =>
        Call("Concept", state, value);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula state = Seq(Open, boolean, Sp, Times, Sp, boolean, Close);
        Formula rule = F.Id("R");
        Formula log = F.Id("L");
        Formula caseReadout = F.Id("C");
        Formula appealOracle = F.Id("appealOracle");
        Formula targetOracle = F.Id("targetOracle");
        Formula appeal = Compose(appealOracle, Join(rule, caseReadout));
        Formula target = Compose(targetOracle, Join(caseReadout, rule));
        Formula appealEqualsTarget = Seq(appeal, Sp, Eq, Sp, target);
        Formula targetRecovery = Call(
            "Refines",
            Call("canonicalTargetReadout", target),
            Join(caseReadout, appeal));
        Formula missingExplanation = new Formula.Not(Call("Refines", rule, log));
        Formula clauses = And(
            appealEqualsTarget,
            And(targetRecovery, missingExplanation));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(FormulaIdentifier.Create("R"), Concept(state, boolean)),
                new(FormulaIdentifier.Create("L"), Concept(state, unit)),
                new(FormulaIdentifier.Create("C"), Concept(state, boolean)),
                new(FormulaIdentifier.Create("appealOracle"),
                    Arrow(Seq(Open, boolean, Sp, Times, Sp, boolean, Close), boolean)),
                new(FormulaIdentifier.Create("targetOracle"),
                    Arrow(Seq(Open, boolean, Sp, Times, Sp, boolean, Close), boolean)),
            ],
            clauses));
    }
}
