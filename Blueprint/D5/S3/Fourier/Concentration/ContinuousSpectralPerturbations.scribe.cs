using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class ContinuousSpectralPerturbationsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent interval offsets give common weighted near-collision bounds.",
        H("Common Spectral Perturbations on Intervals"),
        Blocks(
            Paragraph(Text(
                "Let J and K be countable. Frequencies g(j) have prescribed radii ε(j)>0. Each "
                + "test k has finite support in J, nonnegative weights, a natural degree, a nonnegative "
                + "closed resolution η(k), and a positive excess budget b(k). Write D(k) for the "
                + "diagonal weight and E(k,h) for the weighted collision mass of h on that test's support.")),
            Paragraph(Text(
                "For distinct degree vectors m and n, let L(m,n) be the maximum of "
                + "|m(j)−n(j)| ε(j) over the support. The quantity A(k) sums the products of the "
                + "weighted multinomial coefficients times min(1,η(k)/L(m,n)) over distinct "
                + "ordered pairs. The budget sum is taken in the extended nonnegative reals.")),
            Describe.Lean(
                DescribeId.Create("exists-continuous-common-nearby-bounds"),
                DeclarationHandle.Create(Owner + ".exists_continuous_common_nearby_bounds"),
                H("One perturbation bounds every test's excess"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a distinct pair choose a coordinate attaining L(m,n), which is positive. "
                        + "Fix all other offsets on the support. The closed collision condition is an "
                        + "affine band in the remaining coordinate, with length at most twice the "
                        + "resolution divided by the absolute slope. Intersecting with the perturbation "
                        + "interval and normalizing by its length gives the pairwise factor.")),
                    Paragraph(Text(
                        "Finite marginals give the same distribution on the support of each test. "
                        + "Summing the weighted indicators gives A(k) as an upper bound on expected "
                        + "excess. The expected sum of the excesses divided by b(k) is at most one. "
                        + "An assignment violating any test has total normalized excess strictly "
                        + "above one. The product measure gives full measure to the simultaneous radius "
                        + "constraint, so there is an allowed assignment satisfying all tests.")),
                    Paragraph(Text(
                        "The result constructs a comparison spectrum. A prescribed counting law would "
                        + "also need estimates on threshold crossings, and the fixed zeta ordinates "
                        + "require arithmetic control of their own weighted near-collisions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Bound()
    {
        var j = F.Id("j");
        var k = F.Id("k");
        var spectrum = F.Id("h");
        var index = F.Id("J");
        var tests = F.Id("K");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var budget = Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, tests)),
            new Formula.Fraction(Call("A", k), Call("b", k)));
        var radius = Seq(Varepsilon, Open, j, Close);
        var distance = new Formula.Absolute(Seq(Call("h", j), Minus, Call("g", j)));
        var proximity = Bind(FormulaQuantifier.ForAll, "j", index, AtMost(distance, radius));
        var collision = Bind(FormulaQuantifier.ForAll, "k", tests,
            AtMost(Call("E", k, spectrum), Add(Call("D", k), Call("b", k))));
        var conclusion = Bind(FormulaQuantifier.Exists, "h", Seq(index, Sp, To, Sp, reals),
            new Formula.Logic(proximity, FormulaLogicOperator.And, collision));
        return Disp(new Formula.Logic(AtMost(budget, D(1)), FormulaLogicOperator.Implies, conclusion));
    }
}
