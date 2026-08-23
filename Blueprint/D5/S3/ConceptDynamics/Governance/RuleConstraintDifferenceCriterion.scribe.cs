using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class RuleConstraintDifferenceCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rule factorization excludes arbitrary differences, with the converse isolated to "
            + "finite effective models.",
        H("Rule Constraint and Arbitrary Differences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rule-constraint-difference-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Governance/RuleConstraintDifferenceCriterion."
                        + "rule_constraint_difference_criterion"),
                H("Rule constraint excludes arbitrary differences"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The forward clause is unrestricted. If the decision J factors through "
                            + "the public attribute readout A, two cases with the same public "
                            + "attribute cannot receive different decisions.")),
                    Paragraph(Text(
                        "The converse has its own premise set: the state, attribute, and decision "
                            + "carriers are finite, and A is surjective so its codomain consists "
                            + "only of effective public values. Under those restrictions, absence "
                            + "of an arbitrary-difference pair yields a public rule factorization.")),
                    Paragraph(Text(
                        "The repository's frozen answerability criterion is applied directly in "
                            + "the inhabited case. If the state carrier is empty, surjectivity "
                            + "forces the attribute carrier to be empty and the factorization is "
                            + "constructed by empty elimination."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula Factorization(
        Formula attribute, Formula decision, Formula attributeType, Formula decisionType)
    {
        Formula rule = F.Id("j");
        return Seq(
            Exists, Sp, rule, Colon, Sp, Arrow(attributeType, decisionType), Comma, Sp,
            decision, Sp, Eq, Sp, rule, Sp, Circ, Sp, attribute);
    }

    private static Formula Difference(Formula state, Formula attribute, Formula decision)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Seq(
            Exists, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Apply(attribute, x), Sp, Eq, Sp, Apply(attribute, y), Sp, Land, Sp,
            Apply(decision, x), Sp, Neq, Sp, Apply(decision, y));
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula attributeType = F.Id("B");
        Formula decisionType = F.Id("Y");
        Formula attribute = F.Id("A");
        Formula decision = F.Id("J");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula factorization = Factorization(
            attribute, decision, attributeType, decisionType);
        Formula noDifference = Seq(Neg, Sp, Difference(state, attribute, decision));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, attributeType, Comma, Sp,
            decisionType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            attribute, Colon, Sp, Arrow(state, attributeType), Comma, Sp,
            decision, Colon, Sp, Arrow(state, decisionType), Comma,
            RowBreak, Grp(),
            Open, Open, factorization, Close, Sp, Rightarrow, Sp,
            Open, noDifference, Close, Close,
            Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp,
            Typeclass("Fintype", state), Comma, Sp,
            Typeclass("Fintype", attributeType), Comma, Sp,
            Typeclass("Fintype", decisionType), Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("Surjective")), Open, attribute, Close,
            Sp, Rightarrow, Sp, Open, noDifference, Close,
            Sp, Rightarrow, Sp, Open, factorization, Close,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
