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
                + "ordered pairs. Write C for the sum of A(k)/b(k) in the extended nonnegative reals.")),
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
                        + "excess. The expected normalized sum is at most C. If it exceeded C at "
                        + "every allowed assignment, its integral would be strictly greater than C, "
                        + "since the radius constraint holds almost surely. At a selected assignment "
                        + "every summand is nonnegative and at most the total, which is at most one.")),
                    Paragraph(Text(
                        "Positive radii give interval laws with nonzero length. Countability lets "
                        + "us impose all radius constraints almost surely and integrate the sum of "
                        + "test excesses. Nonnegative weights give nonnegative pair contributions. "
                        + "The nonnegative resolution includes the diagonal, and positive test budgets "
                        + "permit normalization. For two equal starting ordinates with unit radii and "
                        + "weights, a degree-one test at resolution two captures both ordered "
                        + "off-diagonal pairs for every allowed assignment. With excess budget one, "
                        + "C is two and the individual test fails. This computation uses direct arithmetic.")),
                    Paragraph(Text(
                        "The result constructs a comparison spectrum. A prescribed counting law would "
                        + "also need estimates on threshold crossings, and the fixed zeta ordinates "
                        + "require arithmetic control of their own weighted near-collisions."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "More generally, let q(k,m,n) be any extended nonnegative upper bound for the "
                + "probability that the distinct ordered degree pair m,n hits the closed band under the product "
                + "of the normalized intervals on test k's support. Define Cq by replacing the "
                + "single-coordinate factor in A(k) with q(k,m,n) and summing the new A(k)/b(k).")),
            Describe.Lean(
                DescribeId.Create("exists-continuous-common-nearby-bounds-of-pair-probabilities"),
                DeclarationHandle.Create(Owner + ".exists_continuous_common_nearby_bounds_of_pair_probabilities"),
                H("Pair probabilities suffice for a common perturbation"),
                StatementSource.FromAuthor(Bound("Cq")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Divide the expected off-diagonal mass in each finite marginal by its "
                        + "positive budget. The two finite sums integrate term by term and each "
                        + "probability is bounded by q(k,m,n). Integrate the countable sum on "
                        + "the joint product of the original interval measures. An assignment "
                        + "within the intervals attains a normalized total at most Cq."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Bound(string total = "C")
    {
        var j = F.Id("j");
        var k = F.Id("k");
        var spectrum = F.Id("h");
        var index = F.Id("J");
        var tests = F.Id("K");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var budget = F.Id(total);
        var normalizedExcess = new Formula.Fraction(
            Seq(Call("E", k, spectrum), Minus, Call("D", k)), Call("b", k));
        var aggregate = AtMost(Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, tests)),
            normalizedExcess), budget);
        var radius = Seq(Varepsilon, Open, j, Close);
        var distance = new Formula.Absolute(Seq(Call("h", j), Minus, Call("g", j)));
        var proximity = Bind(FormulaQuantifier.ForAll, "j", index, AtMost(distance, radius));
        var collision = Bind(FormulaQuantifier.ForAll, "k", tests,
            AtMost(Call("E", k, spectrum), Add(Call("D", k), Call("b", k))));
        var conclusion = Bind(FormulaQuantifier.Exists, "h", Seq(index, Sp, To, Sp, reals),
            new Formula.Logic(proximity, FormulaLogicOperator.And,
                new Formula.Logic(aggregate, FormulaLogicOperator.And, collision)));
        return Disp(new Formula.Logic(AtMost(budget, D(1)), FormulaLogicOperator.Implies, conclusion));
    }
}
