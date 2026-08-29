using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class CayleyMomentTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/TestFunctions/CayleyMomentTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Resolvent weighting and the Cayley map transport local Fourier moments to the circle.",
        H("Cayley Moment Transport"),
        Blocks(
            Definition(
                "cayley-circle-map",
                "cayleyCircle",
                "Positive-scale Cayley map",
                "The real resolvent Cayley character is bundled on the exact complex unit "
                    + "circle. Positivity of the scale supplies the nonvanishing denominator."),
            Definition(
                "resolvent-density",
                "resolventDensity",
                "Resolvent density",
                "The positive density is the reciprocal of xi squared plus the scale squared."),
            Definition(
                "cayley-compactification",
                "cayleyCompactification",
                "Resolvent Cayley compactification",
                "A positive real-line measure is weighted by the resolvent density and pushed "
                    + "forward through the positive-scale Cayley map."),
            Definition(
                "cayley-inverse-coordinate",
                "cayleyInverse",
                "Cayley inverse coordinate",
                "The real part of the inverse fractional-linear coordinate recovers the real "
                    + "spectral parameter away from the omitted circle point."),
            Definition(
                "cayley-local-moment-function",
                "cayleyMomentFunction",
                "Cayley local moment function",
                "The local circle observable multiplies the Fourier-Laplace transform by the "
                    + "resolvent denominator and takes value zero at the omitted point."),
            Definition(
                "inverse-measure-pairing",
                "inverseMeasurePairing",
                "Inverse-measure pairing",
                "The pairing is the real-line integral of the local Fourier-Laplace transform "
                    + "against the supplied positive measure."),
            Describe.Lean(
                DescribeId.Create("local-fourier-moment-cayley-transport"),
                DeclarationHandle.Create(Prefix + "cayley_moment_transport"),
                H("Local Fourier moments transport through Cayley compactification"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive scale, real-line measure, and Weil test function, "
                            + "the compactified circle moment equals the real Fourier moment "
                            + "and the named inverse-measure pairing.")),
                    Paragraph(Text(
                        "The normalized circle Haar moment is also public and equals twice the "
                            + "scale times the value of the test function at zero. The proof "
                            + "uses the one-dimensional Cayley Jacobian and Schwartz Fourier "
                            + "inversion in the repository convention."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string id,
        string declaration,
        string heading,
        string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula circle = Call("Circle");
        Formula a = F.Id("a"), nu = F.Id("nu"), phi = F.Id("phi");
        Formula xi = F.Id("xi"), z = F.Id("z");
        Formula circleMoment = Integral(
            z,
            circle,
            Call("cayleyMomentFunction", a, phi, z),
            Call("cayleyCompactification", a, nu));
        Formula realMoment = Integral(
            xi,
            real,
            Call("fourierLaplace", phi, xi),
            nu);
        Formula haarMoment = Integral(
            z,
            circle,
            Call("cayleyMomentFunction", a, phi, z),
            Call("normalizedCircleHaar"));
        Formula conclusion = And(
            Equal(circleMoment, realMoment),
            And(
                Equal(circleMoment, Call("inverseMeasurePairing", nu, phi)),
                Equal(
                    haarMoment,
                    Mul(Call("complex", Mul(D(2), a)), Apply(phi, D(0))))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("a", real),
                Bound("nu", Call("Measure", real)),
                Bound("phi", Call("WeilTestFunction"))
            ],
            Implies(Less(D(0), a), conclusion)));
    }

    private static Formula Integral(
        Formula variable, Formula domain, Formula integrand, Formula measure) =>
        Call("integral", variable, domain, integrand, measure);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

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
}
