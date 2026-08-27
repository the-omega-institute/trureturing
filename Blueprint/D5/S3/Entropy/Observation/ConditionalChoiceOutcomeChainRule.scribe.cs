using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class ConditionalChoiceOutcomeChainRuleDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional entropy separates a choice from its subsequent outcome.",
        H("Conditional Choice-Outcome Chain Rule"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-choice-outcome-chain-rule"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Observation/ConditionalChoiceOutcomeChainRule."
                        + "conditional_choice_outcome_chain_rule"),
                H("Choice-outcome conditional entropy obeys the chain rule"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite joint mass is carried directly on public context, choice, "
                            + "and outcome. Its context-choice marginal is the canonical "
                            + "xyProjection.")),
                    Paragraph(Text(
                        "The first summand measures the choice left undecided by the public "
                            + "context; the second measures the outcome left undecided after "
                            + "both context and choice are supplied."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("Q");
        Formula a = F.Id("A");
        Formula y = F.Id("Y");
        Formula p = F.Id("p");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula product(Formula left, Formula right) =>
            Seq(left, Sp, Times, Sp, right);
        Formula entropy(Formula value, Formula given) =>
            Seq(F.Id("H"), Open, value, Sp, Mid, Sp, given, Close);

        Formula carriers = Seq(
            Call("Fintype", q), Sp, Land, Sp,
            Call("Fintype", a), Sp, Land, Sp,
            Call("Fintype", y));
        Formula nonnegative = Seq(
            Forall, Sp, F.Id("z"), Colon, Sp, product(q, product(a, y)), Comma, Sp,
            D(0), Sp, Leq, Sp, new Formula.Apply(p, [F.Id("z")]));
        Formula premise = Seq(carriers, Sp, Land, Sp, nonnegative);
        Formula identity = Seq(
            entropy(product(a, y), q), Sp, Eq, Sp,
            entropy(a, q), Sp, Plus, Sp, entropy(y, product(q, a)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Q"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("A"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), F.Id("Type")),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("p"),
                    Arrow(product(q, product(a, y)), real)),
            ],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, identity)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
