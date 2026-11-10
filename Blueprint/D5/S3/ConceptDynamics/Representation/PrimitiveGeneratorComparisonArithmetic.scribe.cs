using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Representation;

internal sealed class PrimitiveGeneratorComparisonArithmeticDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Representation/PrimitiveGeneratorComparisonArithmetic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational arithmetic core of the primitive-generator versus double-anchor count comparison.",
        H("Primitive-generator comparison arithmetic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("explicit-comparison-strict-reduction"),
                DeclarationHandle.Create(Prefix + "explicit_comparison_strict_reduction"),
                H("The explicit comparison count is strictly reduced"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For rational n, m and d with n at least four, a generating prefix "
                        + "between n and n plus two, and d at least n(n plus one)/2, the "
                        + "generator count md minus m(m plus one)/2 dominates the two-anchor "
                        + "count 2d. The theorem proves both displayed lower bounds and strict "
                        + "positivity. It formalizes the arithmetic comparison only; it does "
                        + "not formalize the Euclidean Jordan algebra generator theorem."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Mul(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Sub(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, right);

    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);

    private static Formula Half(Formula value) =>
        new Formula.Fraction(value, D(2));

    private static Formula Gen(Formula m, Formula d) =>
        Call("generatorComparisonCount", m, d);

    private static Formula Pair(Formula d) =>
        Call("pairComparisonCount", d);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            Seq(Mathbb, Grp(F.Id("Q"))), body);

    private static Formula Formula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula d = F.Id("d");
        Formula nPlusOne = Add(n, D(1));
        Formula nMinusTwo = Sub(n, D(2));
        Formula generatorMinusPair = Sub(Gen(m, d), Pair(d));
        Formula hypotheses = And(
            Le(D(4), n),
            And(Le(n, m),
                And(Le(m, Add(n, D(2))),
                    Le(Half(Mul(n, nPlusOne)), d))));
        Formula conclusion = And(
            Le(Sub(Mul(nMinusTwo, d), Half(Mul(n, nPlusOne))),
                generatorMinusPair),
            And(
                Le(Half(Mul(Mul(n, nPlusOne), Sub(n, D(3)))), generatorMinusPair),
                Lt(generatorMinusPair, D(0))));
        // `Lt(a, 0)` renders the strict positivity as `0 < a` after argument reversal.
        conclusion = And(
            Le(Sub(Mul(nMinusTwo, d), Half(Mul(n, nPlusOne))), generatorMinusPair),
            And(
                Le(Half(Mul(Mul(n, nPlusOne), Sub(n, D(3)))), generatorMinusPair),
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, generatorMinusPair)));
        return Disp(All("n", All("m", All("d", Implies(hypotheses, conclusion)))));
    }
}
