using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class DyadicFourierInversionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/DyadicFourierInversion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier inversion identifies the dyadic convolution density with a smooth inverse transform.",
        H("Dyadic Fourier Inversion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dyadic-density-smoothness"),
                DeclarationHandle.Create(Module + "dyadicConvolutionDensity_contDiff"),
                H("Smoothness of the density"),
                StatementSource.FromAuthor(SmoothnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive width and every natural order k, the previously "
                            + "constructed real density is C^k. This is infinite differentiability. "
                            + "The order is stated with natural numbers because the outer top "
                            + "of the pinned smoothness index denotes analyticity.")),
                    Paragraph(Text(
                        "Apply Mathlib's weighted-integrability theorem to the transform, "
                            + "compose with negation to obtain its inverse transform, and take "
                            + "the real part. The inversion identity below identifies this "
                            + "smooth function with the actual pointwise convolution limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-density-fourier-inversion"),
                DeclarationHandle.Create(Module + "dyadic_density_eq_fourier_inversion"),
                H("Pointwise inversion"),
                StatementSource.FromAuthor(InversionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Fourier-Laplace transform uses the positive exponential exp(i*z*x). "
                            + "Mathlib's Fourier transform uses exp(-2*pi*i*xi*x), so its "
                            + "frequency equals -2*pi*xi in the former convention. The formula "
                            + "uses Mathlib's inverse transform of this rescaled function.")),
                    Paragraph(Text(
                        "The frozen finite-convolution Lipschitz estimate passes to the "
                            + "pointwise limit and gives continuity. The frozen order-zero "
                            + "weighted integrability, after the frequency substitution, "
                            + "supplies the other hypothesis of Mathlib's Fourier inversion theorem."))),
                DescribeRole.Theorem))));

    private static Formula SmoothnessFormula() => Disp(ForAll("ell", Call("Real"),
        Implies(Less(D(0), F.Id("ell")), ForAll("k", Call("Natural"),
            Call("ContDiff", Call("Real"), F.Id("k"), Density())))));

    private static Formula InversionFormula()
    {
        Formula frequency = Multiply(Multiply(new Formula.Negate(D(2)), Call("pi")), F.Id("xi"));
        Formula transform = Lambda("xi", Call("Real"),
            Call("densityFourierLaplace", Density(), frequency));
        return Disp(ForAll("ell", Call("Real"), Implies(Less(D(0), F.Id("ell")),
            ForAll("x", Call("Real"), new Formula.Relation(
                Call("dyadicConvolutionDensity", F.Id("ell"), F.Id("x")),
                FormulaRelationOperator.Equal,
                Call("re", Call("fourierInv", transform, F.Id("x"))))))));
    }

    private static Formula Density() => Call("dyadicConvolutionDensity", F.Id("ell"));

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
