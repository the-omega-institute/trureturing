using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaCore;

internal sealed class ResolventParitySignaturesDocument : IScribeDocumentDefinition
{
    private const string Handle = "D5/S3/Weil/ZetaCore/ResolventParitySignatures.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local spectral correlations have a hyperbolic difference mode with opposite parity signs.",
        H("Resolvent Parity Signatures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-completion-difference"),
                DeclarationHandle.Create(Handle + "local_completion_difference"),
                H("Local completion difference"),
                StatementSource.FromAuthor(LocalDifferenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The correlations are constructed directly from the two real spectral "
                        + "measures. Shared local Green derivative data cancels in their "
                        + "difference, while the cosine kernel supplies evenness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cosh-correlation-signature"),
                DeclarationHandle.Create(Handle + "cosh_correlation_signature"),
                H("Hyperbolic cosine correlation signature"),
                StatementSource.FromAuthor(CorrelationSignatureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For smooth compactly supported complex functions, the convolution with "
                        + "involution is paired directly against the hyperbolic cosine kernel. "
                        + "The two bilateral exponential identities yield the positive even "
                        + "channel product minus the odd channel product."))),
                DescribeRole.Theorem))));

    private static Formula LocalDifferenceFormula()
    {
        Formula real = Call("Real");
        Formula L = F.Id("L"), a = F.Id("a");
        Formula nu = F.Id("nu"), mu = F.Id("mu");
        Formula Dnu = F.Id("Dnu"), Dmu = F.Id("Dmu"), source = F.Id("source");
        Formula t = F.Id("t");

        Formula Local(Formula body) =>
            AllReal(Implies(InLocalInterval(t, L), body), t);
        Formula FirstData(Formula measure, Formula derivative) => Local(
            Call("HasDerivAt", Lambda(t, Correlation(measure, a, t)),
                Apply(derivative, t), t));
        Formula SecondData(Formula measure, Formula derivative) => Local(
            Call("HasDerivAt", derivative,
                Add(Mul(Pow(a, D(2)), Correlation(measure, a, t)), Apply(source, t)), t));

        Formula assumptions = All(
            Less(D(0), L),
            FirstData(nu, Dnu),
            FirstData(mu, Dmu),
            SecondData(nu, Dnu),
            SecondData(mu, Dmu));
        Formula conclusion = AllReal(
            Implies(
                Less(new Formula.Absolute(t), Mul(D(2), L)),
                Equal(
                    Sub(Correlation(nu, a, t), Correlation(mu, a, t)),
                    Mul(
                        Sub(Correlation(nu, a, D(0)), Correlation(mu, a, D(0))),
                        Call("cosh", Mul(a, t))))),
            t);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("L", real),
                Bound("a", real),
                Bound("nu", Call("Measure", real)),
                Bound("mu", Call("Measure", real)),
                Bound("Dnu", Arrow(real, real)),
                Bound("Dmu", Arrow(real, real)),
                Bound("source", Arrow(real, real)),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula CorrelationSignatureFormula()
    {
        Formula real = Call("Real"), complex = Call("Complex");
        Formula a = F.Id("a"), f = F.Id("f"), h = F.Id("h");
        Formula functionType = Arrow(real, complex);
        Formula assumptions = All(
            Call("ContDiff", real, Call("infinity"), f),
            Call("HasCompactSupport", f),
            Call("ContDiff", real, Call("infinity"), h),
            Call("HasCompactSupport", h));
        Formula conclusion = Equal(
            HyperbolicPairing(a, f, h, real),
            Sub(
                Mul(EvenChannel(a, f, real), Call("conj", EvenChannel(a, h, real))),
                Mul(OddChannel(a, f, real), Call("conj", OddChannel(a, h, real)))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", real), Bound("f", functionType), Bound("h", functionType)],
            Implies(assumptions, conclusion)));
    }

    private static Formula Correlation(Formula measure, Formula a, Formula time)
    {
        Formula xi = F.Id("xi"), real = Call("Real");
        Formula numerator = Call("cos", Mul(time, xi));
        Formula denominator = Add(Pow(xi, D(2)), Pow(a, D(2)));
        return Integral(xi, real, new Formula.Fraction(numerator, denominator), measure);
    }

    private static Formula HyperbolicPairing(
        Formula a, Formula f, Formula h, Formula real)
    {
        Formula t = F.Id("t"), x = F.Id("x");
        Formula involution = Lambda(x, Call("conj", Apply(h, new Formula.Negate(x))));
        Formula convolution = Call("convolution", f, involution);
        Formula integrand = Mul(
            Call("complex", Call("cosh", Mul(a, t))),
            Apply(convolution, t));
        return Integral(t, real, integrand, Call("volume"));
    }

    private static Formula EvenChannel(Formula a, Formula f, Formula real)
    {
        Formula x = F.Id("x");
        return Integral(x, real,
            Mul(Call("complex", Call("cosh", Mul(a, x))), Apply(f, x)),
            Call("volume"));
    }

    private static Formula OddChannel(Formula a, Formula f, Formula real)
    {
        Formula x = F.Id("x");
        return Integral(x, real,
            Mul(Call("complex", Call("sinh", Mul(a, x))), Apply(f, x)),
            Call("volume"));
    }

    private static Formula Integral(
        Formula variable, Formula domain, Formula integrand, Formula measure) =>
        Call("integral", variable, domain, integrand, measure);

    private static Formula InLocalInterval(Formula t, Formula L) =>
        Call("InOpenInterval", t, Call("neg", Mul(D(2), L)), Mul(D(2), L));

    private static Formula Lambda(Formula variable, Formula body) =>
        Call("lambda", variable, body);

    private static Formula AllReal(Formula body, Formula variable) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            ((Formula.LatexWord)variable).Value,
            Call("Real"),
            body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }
}
