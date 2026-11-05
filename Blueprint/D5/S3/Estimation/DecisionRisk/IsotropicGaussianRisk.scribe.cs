using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class IsotropicGaussianRiskDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk.";
    private static Formula V => F.Id("V");
    private static Formula MuZero => F.Id("muZero");
    private static Formula MuOne => F.Id("muOne");
    private static Formula Sigma => F.Id("sigma");
    private static Formula X => F.Id("x");
    private static Formula Q => F.Id("q");
    private static Formula Mid => Call("midpoint", MuZero, MuOne);
    private static Formula Region => Call("region", MuZero, MuOne);
    private static Formula Separation => Seq(Vert, Sp, Sub(MuOne, MuZero), Vert, Sp);
    private static Formula Tail => Call("phi", Div(Seq(Minus, Separation), Mul(D(2), Sigma)));
    private static Formula Function => Seq(V, Sp, To, Sp, Real());

    public DocumentDefinition Create()
    {
        Formula affine = LambdaOf("z", V, Add(F.Id("mu"), Mul(Sigma, F.Id("z"))));
        Formula lawStatement = Ambient(All("mu", V, All("sigma", Real(),
            Eqn(Call("law", F.Id("mu"), Sigma), Call("map", Call("stdGaussian", V), affine)))));
        Formula firstError = Call("integral", LambdaOf("x", V, Apply(Q, X)), Call("law", MuZero, Sigma));
        Formula secondError = Call("integral", LambdaOf("x", V, Sub(D(1), Apply(Q, X))), Call("law", MuOne, Sigma));
        Formula riskStatement = MeansAndScale(All("q", Function,
            Eqn(Risk(Q), Div(Add(firstError, secondError), D(2)))));
        Formula phiStatement = All("t", Real(), Eqn(Call("phi", F.Id("t")),
            Call("measureReal", Call("gaussianReal", D(0), D(1)), Call("Iic", F.Id("t")))));
        Formula centre = Mul(Div(D(1), D(2)), Paren(Add(MuZero, MuOne)));
        Formula regionPredicate = LeF(D(0), Call("inner", Sub(MuOne, MuZero), Sub(X, centre)));
        Formula regionStatement = Means(Eqn(Region, Call("setOf", LambdaOf("x", V, regionPredicate))));
        Formula midpointStatement = Means(Eqn(Mid, Call("indicator", Region, Call("constantOne", V))));
        Formula allRules = All("q", Function,
            Implies(Call("Measurable", Q), Bounded(Q), LeF(Tail, Risk(Q))));
        Formula optimum = MeansAndScale(Implies(LtF(D(0), Sigma),
            And(Call("Measurable", Mid), Bounded(Mid), Eqn(Risk(Mid), Tail), allRules)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The midpoint rule attains the exact equal-prior risk against every measurable randomized rule for two isotropic Gaussian laws.",
            H("Exact Isotropic Gaussian Binary Risk"),
            Blocks(
                Definition("law", "Affine Gaussian law", lawStatement,
                    "The law is the pushforward of the standard Gaussian by z mapped to mu plus sigma times z. "
                        + "The real noise scale in this definition is unrestricted; the optimum theorem assumes it is positive."),
                Definition("risk", "Equal-prior randomized risk", riskStatement,
                    "A rule q returns the probability of choosing label one. Its two class-conditional errors are the integrals "
                        + "of q under the first law and of one minus q under the second. The risk averages these two errors."),
                Definition("phi", "Standard Gaussian distribution function", phiStatement,
                    "Phi is the real measure of the closed lower half-line under the standard one-dimensional Gaussian. "
                        + "The variance parameter is one."),
                Definition("region", "Midpoint decision region", regionStatement,
                    "The region contains exactly the observations whose inner product with the mean difference, after centering "
                        + "at the midpoint of the means, is nonnegative. Ties choose label one."),
                Definition("midpoint", "Midpoint randomized rule", midpointStatement,
                    "The midpoint rule is the real-valued indicator of the midpoint region. It takes only zero and one, "
                        + "and is also an admissible randomized rule."),
                Describe.Lean(
                    DescribeId.Create("isotropic-gaussian-optimal"),
                    DeclarationHandle.Create(Owner + "isotropic_gaussian_optimal"),
                    H("Exact optimum over all measurable randomized rules"),
                    StatementSource.FromAuthor(Disp(optimum)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be any finite-dimensional real inner-product space with its Borel measurable structure. "
                            + "The means are arbitrary and sigma is positive. The theorem gives a measurable admissible "
                            + "midpoint rule, evaluates its risk as Phi of minus the mean separation divided by twice sigma, "
                            + "and bounds every measurable real-valued rule in the interval from zero to one by the same value. "
                            + "Every finite coordinate type is allowed, including the empty type.")),
                    Paragraph(Text(
                        "In orthonormal coordinates, the isotropic covariance matrix has square root sigma times the identity. "
                            + "The multivariate Gaussian density formula therefore gives both laws a common positive finite "
                            + "normalization C and densities C times exp of minus the squared distance to the corresponding mean "
                            + "divided by twice sigma squared. The determinant expression makes C independent of the mean. "
                            + "The product of one-dimensional densities becomes this squared-norm exponential, and the "
                            + "orthonormal coordinate equivalence preserves volume. The empty coordinate product remains included.")),
                    Paragraph(Text(
                        "The difference of the squared distances to the two means equals twice the inner product defining "
                            + "the midpoint region. Inside that region the first density is no greater, with equality on ties. The excess integrand of an "
                            + "arbitrary rule over the midpoint rule is then one minus q times the difference of the densities. "
                            + "Outside the region it is q times the opposite density difference. Both are nonnegative. "
                            + "Bounded measurable rules are integrable under the probability laws; changing measure with the "
                            + "actual densities and integrating this pointwise inequality gives the bound for every such rule.")),
                    Paragraph(Text(
                        "For distinct means, projection of centered standard Gaussian noise Z onto their unit separation vector has standard Gaussian law, before the mean shift and noise scaling. "
                            + "The two midpoint error events become upper and strict lower half-lines at the corresponding "
                            + "half-separation thresholds. Gaussian reflection and the zero measure of a singleton evaluate both "
                            + "tails exactly. When the means coincide, the two risk integrands add to one and every admissible "
                            + "rule has risk one half. This also includes zero-dimensional spaces. The rule class here consists "
                            + "of measurable probability functions; a Markov-kernel formulation additionally requires its own "
                            + "risk-preserving correspondence."))),
                DescribeRole.Theorem))));
    }

    private static DocumentBlock Definition(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("isotropic-gaussian-" + name), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Ambient(Formula body) => All("V", F.Id("Type"), Seq(
        Instance(Call("NormedAddCommGroup", V)), Sp,
        Instance(Call("InnerProductSpace", Real(), V)), Sp,
        Instance(Call("FiniteDimensional", Real(), V)), Sp,
        Instance(Call("MeasurableSpace", V)), Sp,
        Instance(Call("BorelSpace", V)), Comma, RowBreak, Grp(), body));
    private static Formula Means(Formula body) => Ambient(All("muZero", V, All("muOne", V, body)));
    private static Formula MeansAndScale(Formula body) => Means(All("sigma", Real(), body));
    private static Formula Bounded(Formula function) => All("x", V,
        And(LeF(D(0), Apply(function, X)), LeF(Apply(function, X), D(1))));
    private static Formula Risk(Formula function) => Call("risk", MuZero, MuOne, Sigma, function);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Instance(Formula value) => Seq(OpenBracket, value, CloseBracket);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Lambda, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Implies(params Formula[] terms) => Infix(Rightarrow, terms);
    private static Formula And(params Formula[] terms) => Infix(Land, terms);
    private static Formula Add(params Formula[] terms) => Infix(Plus, terms);
    private static Formula Sub(params Formula[] terms) => Infix(Minus, terms);
    private static Formula Mul(params Formula[] terms) => Infix(Cdot, terms);
    private static Formula Infix(Formula op, Formula[] terms)
    {
        var items = new List<Formula> { Open };
        for (var i = 0; i < terms.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, op, Sp]);
            items.AddRange([Open, terms[i], Close]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Div(Formula numerator, Formula denominator) => Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula LtF(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula LeF(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
}
