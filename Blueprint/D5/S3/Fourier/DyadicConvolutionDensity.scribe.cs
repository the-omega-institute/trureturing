using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class DyadicConvolutionDensityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/DyadicConvolutionDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dyadic convolution limit is a compactly supported probability density "
            + "with the prescribed infinite sinc transform.",
        H("Dyadic Convolution Density"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dyadic-density-realizes-infinite-sinc-transform"),
                DeclarationHandle.Create(Module + "dyadicConvolutionDensity_fourierLaplace"),
                H("The limiting density has the infinite sinc transform"),
                StatementSource.FromAuthor(LimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The density is the pointwise limit of the finite convolutions of "
                            + "the uniform densities with half-width ell/2^(j+2), starting at "
                            + "j=0. Two components give a Lipschitz density. Subsequent "
                            + "convolution preserves its Lipschitz bound, and adding a "
                            + "component of half-width a changes its value by at most L*a. "
                            + "Summability of the widths proves the Cauchy property.")),
                    Paragraph(Text(
                        "The accompanying theorems prove nonnegativity, evenness, "
                            + "integrability, integral one, and topological support contained "
                            + "in [-ell/2, ell/2]. A common compactly supported bound passes "
                            + "the integral and the complex Fourier-Laplace transform through "
                            + "the limit by dominated convergence.")),
                    Paragraph(Text(
                        "The transform uses exp(I*z*x), as do the frozen uniform factors. "
                            + "The finite-convolution identity below identifies the transform "
                            + "limit with the previously frozen sinc product. Smoothness of "
                            + "all orders and polynomial decay are outside this statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-dyadic-convolutions-transform-to-products"),
                DeclarationHandle.Create(Module + "dyadic_partial_convolution_fourierLaplace"),
                H("The finite convolution transform bridge"),
                StatementSource.FromAuthor(FiniteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Index n denotes n+1 components, indexed from zero through n. "
                        + "Multiplication by exp(I*z*x) commutes with convolution in the "
                        + "required weighted form. Applying the integral convolution formula "
                        + "and induction gives the finite product, including nonreal z."))),
                DescribeRole.Theorem))));

    private static Formula LimitFormula()
    {
        Formula ell = F.Id("ell");
        Formula z = F.Id("z");
        Formula j = F.Id("j");
        Formula width = Call("dyadicHalfWidth", ell, j);
        Formula product = Call("tprod", Lambda("j", Call("Natural"),
            Call("complexSinc", Multiply(width, z))));
        return Disp(ForAll(
            [Bound("ell", Call("Real"))],
            Implies(Less(D(0), ell), ForAll(
                [Bound("z", Call("Complex"))],
                Equal(Call("densityFourierLaplace", Call("dyadicConvolutionDensity", ell), z),
                    product)))));
    }

    private static Formula FiniteFormula()
    {
        Formula ell = F.Id("ell");
        Formula n = F.Id("n");
        Formula z = F.Id("z");
        Formula j = F.Id("j");
        Formula product = Call("prod", Call("range", Add(n, D(1))),
            Lambda("j", Call("Natural"),
                Call("uniformIntervalFourierLaplace", Call("dyadicHalfWidth", ell, j), z)));
        return Disp(ForAll(
            [Bound("ell", Call("Real")), Bound("n", Call("Natural")),
                Bound("z", Call("Complex"))],
            Equal(Call("densityFourierLaplace", Call("dyadicPartialConvolution", ell, n), z),
                product)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
