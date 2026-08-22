using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class CommonRuleInformationConvergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Correct common facts align a shared rule, while distinct rules can still disagree.",
        H("Common-Rule Information Convergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-rule-information-convergence"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/CommonRuleInformationConvergence."
                        + "common_rule_information_convergence"),
                H("Common facts align shared rules but not distinct rules"),
                StatementSource.FromAuthor(ConvergenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The target is the canonical concept readout from source states to fully "
                            + "disclosed fact values. Two fact values are sufficient here when each "
                            + "is equal to that target value.")),
                    Paragraph(Text(
                        "The first public conjunct applies one deterministic rule to two correct "
                            + "fact values. The second public conjunct applies distinct rules at a "
                            + "disclosed target value and preserves their disagreement.")),
                    Paragraph(Text(
                        "Repository searches found no theorem containing both clauses. The existing "
                            + "disclosure-defect result instead concerns collisions and consequence "
                            + "recovery. The proof directly applies equality transport."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula ConvergenceFormula()
    {
        Formula source = F.Id("X");
        Formula factType = F.Id("Z");
        Formula decisionType = F.Id("U");
        Formula target = F.Id("T");
        Formula shared = F.Id("d");
        Formula leftRule = Subscript(F.Id("d"), F.Id("i"));
        Formula rightRule = Subscript(F.Id("d"), F.Id("j"));
        Formula x = F.Id("x");
        Formula leftFact = Subscript(F.Id("z"), F.Id("i"));
        Formula rightFact = Subscript(F.Id("z"), F.Id("j"));
        Formula disclosed = F.Id("z");
        Formula targetAtX = Apply(target, x);
        Formula sameRuleClause = Seq(
            Forall, Sp, x, Colon, Sp, source, Comma, Sp,
            leftFact, Comma, Sp, rightFact, Colon, Sp, factType, Comma, Sp,
            Open,
            leftFact, Sp, Eq, Sp, targetAtX, Sp, Land, Sp,
            rightFact, Sp, Eq, Sp, targetAtX,
            Close, Sp, Rightarrow, Sp,
            Apply(shared, leftFact), Sp, Eq, Sp, Apply(shared, rightFact));
        Formula distinctRuleClause = Seq(
            Forall, Sp, x, Colon, Sp, source, Comma, Sp,
            disclosed, Colon, Sp, factType, Comma, Sp,
            Open,
            targetAtX, Sp, Eq, Sp, disclosed, Sp, Land, Sp,
            Apply(leftRule, disclosed), Sp, Neq, Sp, Apply(rightRule, disclosed),
            Close, Sp, Rightarrow, Sp,
            Apply(leftRule, targetAtX), Sp, Neq, Sp, Apply(rightRule, targetAtX));

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, factType, Comma, Sp, decisionType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            target, Colon, Sp, Arrow(source, factType), Comma, Sp,
            shared, Comma, Sp, leftRule, Comma, Sp, rightRule,
            Colon, Sp, Arrow(factType, decisionType), Comma, Esc,
            Open, sameRuleClause, Close, Sp, Land, Esc,
            Open, distinctRuleClause, Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
