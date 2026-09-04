using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class ScalarUnitDressingDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Dilation/ScalarUnitDressing."
            + "nonzero_scalar_dressing_preserves_zero_and_analytic_order";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonvanishing analytic scalar dressing preserves zeros and their multiplicities.",
        H("Scalar Unit Dressing"),
        Blocks(Describe.Lean(
            DescribeId.Create("nonzero-scalar-dressing-preserves-zeros-and-orders"),
            DeclarationHandle.Create(Declaration),
            H("A scalar unit does not move a zero"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let f and g be complex-valued functions analytic at s, with g(s) nonzero. "
                        + "Then multiplying f by g neither creates nor removes a zero at s, "
                        + "and the analytic order at s is unchanged.")),
                Paragraph(Text(
                    "The nonvanishing assumption is the scalar-unit hypothesis. Analyticity "
                        + "of both factors is stated explicitly because pointwise "
                        + "nonvanishing alone does not define or preserve analytic zero order.")),
                Paragraph(Text(
                    "The proof uses Mathlib's zero-product criterion and additive formula for "
                        + "analytic orders. The order of g is zero because it is analytic and "
                        + "nonzero at the chosen point."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula functionType = Seq(complex, Sp, To, Sp, complex);
        Formula f = F.Id("f"), g = F.Id("g"), s = F.Id("s");
        Formula fAtS = Apply(f, s), gAtS = Apply(g, s);
        Formula productAtS = Seq(gAtS, Sp, Cdot, Sp, fAtS);
        Formula productFunction = Seq(g, Sp, Cdot, Sp, f);

        Formula premises = And(
            Call("AnalyticAt", complex, f, s),
            And(
                Call("AnalyticAt", complex, g, s),
                NotEqualTo(gAtS, D(0))));
        Formula zeroIdentity = Iff(
            EqualTo(productAtS, D(0)),
            EqualTo(fAtS, D(0)));
        Formula orderIdentity = EqualTo(
            Call("analyticOrderAt", productFunction, s),
            Call("analyticOrderAt", f, s));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("f", functionType),
                Bound("g", functionType),
                Bound("s", complex),
            ],
            Implies(premises, And(zeroIdentity, orderIdentity))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Not(EqualTo(left, right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
