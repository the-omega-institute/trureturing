using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class LocalizedCollisionBudgetsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/LocalizedCollisionBudgets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise reach and Euclidean scale refine a common perturbation budget.",
        H("Pairwise Bounds for a Common Spectral Perturbation"),
        Blocks(
            Paragraph(Text(
                "Let J and K be countable and let r(j)>0 be the permitted frequency radii. Test k "
                + "uses a finite support, nonnegative weights, natural degree, nonnegative closed "
                + "resolution η(k), and positive budget b(k). Write D(k) for the diagonal and "
                + "E(k,h) for the weighted collision mass of spectrum h on the support.")),
            Paragraph(Text(
                "For a distinct degree pair m,n put a(j)=m(j)−n(j), A=Σ|a(j)|r(j), "
                + "M=max |a(j)|r(j), and S=Σ(a(j)r(j))². Its probability budget is zero when "
                + "the absolute original frequency difference exceeds η(k)+A. Otherwise "
                + "the budget is the minimum of one, η(k)/M, and exp(1/2)√(15π/2)η(k)/√S. "
                + "Set C to the sum of these bounds times the products of multinomial weights "
                + "divided by the positive test budgets. The pairs are ordered.")),
            Describe.Lean(
                DescribeId.Create("exists-continuous-common-nearby-localized-bounds"),
                DeclarationHandle.Create(Owner + ".exists_continuous_common_nearby_localized_bounds"),
                H("One spectrum realizes the weighted pairwise bounds"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the product of the normalized uniform interval measures, the shift "
                        + "of the pair difference is Σa(j)x(j). Almost surely its modulus is at "
                        + "most A. This makes the pair event null in the strictly separated "
                        + "case. For the other pairs, a nonzero difference and positive radii "
                        + "give positive M and S. The one-coordinate and Euclidean estimates "
                        + "bound the same event in the same marginal.")),
                    Paragraph(Text(
                        "Use the common perturbation theorem for these pair probabilities. "
                        + "Finite marginals integrate the weighted off-diagonal terms and one "
                        + "assignment satisfies all the normalized budgets. At the separation "
                        + "boundary the closed band can still be reached. The bound concerns "
                        + "perturbed comparison spectra. The arithmetic estimate for the fixed "
                        + "zeta ordinates remains open."))),
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
        var budget = F.Id("C");
        var normalizedExcess = new Formula.Fraction(
            Seq(Call("E", k, spectrum), Minus, Call("D", k)), Call("b", k));
        var aggregate = AtMost(Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, tests)),
            normalizedExcess), budget);
        var radius = Call("r", j);
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
