using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class DyadicTransformDecayDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/DyadicTransformDecay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real-axis transform of the dyadic convolution density has integrable "
            + "polynomial weights of every natural order.",
        H("Dyadic Transform Decay"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dyadic-density-transform-polynomial-integrability"),
                DeclarationHandle.Create(Module + "dyadic_density_transform_decay"),
                H("Every polynomial weight is integrable"),
                StatementSource.FromAuthor(IntegrabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The transform is the positive-sign Fourier-Laplace integral "
                            + "of the previously constructed density, evaluated at a real "
                            + "frequency. Its frozen identity with the infinite sinc product "
                            + "connects the estimate to that actual density.")),
                    Paragraph(Text(
                        "At order k, use the decay estimate of order k+2. Outside the "
                            + "unit interval the weighted norm is bounded by C/|xi|^2; "
                            + "inside, each sinc factor has norm at most one. Together "
                            + "these give a constant multiple of the integrable function "
                            + "1/(1+xi^2). Measurability follows from the finite products "
                            + "and their pointwise limit.")),
                    Paragraph(Text(
                        "This statement supplies weighted integrability. Fourier inversion "
                            + "and infinite differentiability of the density remain outside "
                            + "this module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sinc-product-arbitrary-order-tail-bound"),
                DeclarationHandle.Create(Module + "sinc_product_decay_bound"),
                H("Arbitrary inverse-power decay"),
                StatementSource.FromAuthor(DecayFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Retain the first k factors. Their norms are bounded by "
                        + "1/(a_j*|xi|), where a_j=ell/2^(j+2) for j starting at zero. "
                        + "Every remaining real-axis factor has norm at most one. "
                        + "Passing the finite-product inequality through the convergent "
                        + "product gives C equal to the product of the first k inverse "
                        + "half-widths. This estimate is the active intermediate result "
                        + "used in the weighted-integrability proof."))),
                DescribeRole.Theorem))));

    private static Formula TransformNorm(Formula ell, Formula xi) =>
        Call("norm", Call("densityFourierLaplace", Call("dyadicConvolutionDensity", ell), xi));

    private static Formula IntegrabilityFormula()
    {
        Formula ell = F.Id("ell");
        Formula xi = F.Id("xi");
        Formula k = F.Id("k");
        return Disp(ForAll([Bound("ell", Call("Real"))],
            Implies(Less(D(0), ell), ForAll([Bound("k", Call("Natural"))],
                Call("Integrable", Lambda("xi", Call("Real"),
                    Multiply(new Formula.Power(Call("abs", xi), k), TransformNorm(ell, xi))))))));
    }

    private static Formula DecayFormula()
    {
        Formula ell = F.Id("ell");
        Formula xi = F.Id("xi");
        Formula k = F.Id("k");
        Formula c = F.Id("C");
        return Disp(ForAll([Bound("ell", Call("Real"))],
            Implies(Less(D(0), ell), ForAll([Bound("k", Call("Natural"))],
                new Formula.BindMany(FormulaQuantifier.Exists, [Bound("C", Call("Real"))],
                    new Formula.Logic(Less(D(0), c), FormulaLogicOperator.And,
                        ForAll([Bound("xi", Call("Real"))],
                            Implies(LessEqual(D(1), Call("abs", xi)),
                                LessEqual(TransformNorm(ell, xi),
                                    new Formula.Fraction(c, new Formula.Power(Call("abs", xi), k)))))))))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
