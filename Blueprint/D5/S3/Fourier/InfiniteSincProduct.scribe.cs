using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class InfiniteSincProductDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/InfiniteSincProduct."
            + "dyadic_uniform_convolution_product_ne_zero_off_real";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic uniform-interval Fourier factors form a sinc product nonzero off the real axis.",
        H("Infinite Sinc Product"),
        Blocks(Describe.Lean(
            DescribeId.Create("dyadic-uniform-sinc-product-is-nonzero-off-the-real-axis"),
            DeclarationHandle.Create(Declaration),
            H("The dyadic sinc product is nonzero away from the real axis"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For positive ell, the nth half-width is ell divided by 2^(n+2). "
                        + "Each associated uniform interval density is nonnegative, even, "
                        + "integrable, and has integral one. Its complex Fourier-Laplace "
                        + "transform is the corresponding removable sinc factor.")),
                Paragraph(Text(
                    "The half-widths sum to ell/2 and their squares are summable. A quadratic "
                        + "estimate for complex sinc minus one gives uniform convergence of "
                        + "the product on every compact subset of the complex plane.")),
                Paragraph(Text(
                    "Every factor is nonzero at a point with nonzero imaginary part. Absolute "
                        + "summability of the factor deviations then prevents the infinite "
                        + "product itself from vanishing there.")),
                Paragraph(Text(
                    "This theorem records the interval components, their exact transform "
                        + "factors, and the infinite-product conclusion. It does not construct "
                        + "the limiting convolution density or assert smoothness and decay."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Natural");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula ell = F.Id("ell");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula z = F.Id("z");
        Formula k = F.Id("K");

        Formula Width(Formula index) => Call("dyadicHalfWidth", ell, index);
        Formula Density(Formula index, Formula point) =>
            Call("uniformIntervalDensity", Width(index), point);
        Formula DensityFunction(Formula index) =>
            Call("uniformIntervalDensity", Width(index));
        Formula Transform(Formula index, Formula point) =>
            Call("uniformIntervalFourierLaplace", Width(index), point);
        Formula Factor(Formula index, Formula point) =>
            Call("complexSinc", Multiply(Width(index), point));
        Formula ProductAt(Formula point) => Call(
            "tprod",
            new Formula.Sequence(Factor(n, point), n, natural));

        Formula intervalData = ForAll(
            [Bound("n", natural)],
            All(
                Less(D(0), Width(n)),
                ForAll(
                    [Bound("x", real)],
                    LessOrEqual(D(0), Density(n, x))),
                ForAll(
                    [Bound("x", real)],
                    Equal(Density(n, new Formula.Negate(x)), Density(n, x))),
                Call("Integrable", DensityFunction(n)),
                Equal(Call("integral", DensityFunction(n)), D(1)),
                ForAll(
                    [Bound("z", complex)],
                    Equal(Transform(n, z), Factor(n, z)))));

        Formula totalWidth = Equal(
            Call("tsum", new Formula.Sequence(Width(n), n, natural)),
            new Formula.Fraction(ell, D(2)));
        Formula factorTable = Lambda(
            [Bound("n", natural), Bound("z", complex)],
            Factor(n, z));
        Formula productFunction = Lambda([Bound("z", complex)], ProductAt(z));
        Formula compactUniformProduct = ForAll(
            [Bound("K", Call("Set", complex))],
            Implies(
                Call("IsCompact", k),
                Call("HasProdUniformlyOn", factorTable, productFunction, k)));
        Formula offRealNonzero = ForAll(
            [Bound("z", complex)],
            Implies(
                NotEqual(Call("im", z), D(0)),
                NotEqual(ProductAt(z), D(0))));

        return Disp(ForAll(
            [Bound("ell", real)],
            Implies(
                Less(D(0), ell),
                All(intervalData, totalWidth, compactUniformProduct, offRealNonzero))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Lambda(Formula.BoundVariable[] variables, Formula body)
    {
        var binders = new List<Formula>();
        for (var index = 0; index < variables.Length; index++)
        {
            if (index > 0)
            {
                binders.Add(Comma);
                binders.Add(Sp);
            }

            binders.Add(F.Id(variables[index].Name.Value));
            binders.Add(Colon);
            binders.Add(Sp);
            binders.Add(variables[index].Domain);
        }

        return Seq(Open, Seq([.. binders]), Sp, Mapsto, Sp, body, Close);
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
