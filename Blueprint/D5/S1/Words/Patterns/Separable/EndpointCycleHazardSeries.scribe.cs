using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointCycleHazardSeriesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The one-cycle hit probability of the actual marked-cycle law is the sum of its zero-discard term and its normalized positive-discard series.",
        H("The actual one-cycle hit probability"),
        Blocks(
            Definition("hit", "Hit of a single actual cycle",
                "At a direct terminal, the terminal permutation must occupy the current diagonal. A skew terminal never hits. A direct discard leaves the discrepancy unchanged, while a skew discard increases it by the length of the discarded shape. The event is then checked on the remaining cycle."),
            Definition("nextHazard", "One-cycle hit probability",
                "At integer discrepancy e, nextHazard is the mass of the hit event under the existing actual marked-cycle law. A direct terminal hits when its actual permutation occupies the diagonal at the current discrepancy. A skew terminal cannot hit. A skew discard of length n+1 increases the discrepancy by n+1, whereas a direct discard leaves it unchanged."),
            Definition("normalizedSkewIterate", "Normalized skew-removal iteration",
                "The zeroth iterate is the actual direct-terminal hit mass. Each application of the operator sums over actual removed shapes. A shape of length n+1 contributes its weight rho^(n+1) divided by b, and its successor is evaluated at e+n+1. The normalization uses the same b as the critical shape law."),
            Paragraph(Text(
                "Write H(e) for nextHazard(e), O(e) for rawOccupation(e), and U(k,e) for normalizedSkewIterate(k,e). In the formula B is ofReal(b), all arithmetic outside ofReal is in the extended nonnegative reals, and the summation is over all natural numbers, starting at zero.")),
            Describe.Lean(DescribeId.Create("actual-endpoint-hazard-normalized-series"),
                DeclarationHandle.Create(Owner + "nextHazard_eq_normalized_series"),
                H("Exact normalized series"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The zero-discard direct terminal contributes exactly ofReal(O(e)). For r at least zero, the starting-skew pattern with 2r+1 discards and the starting-direct pattern with 2r+2 discards each contain r+1 skew removals. The other two parity patterns cannot hit because they end skew.")),
                    Paragraph(Text("The fixed-count law reindexes the actual marked-cycle hit event without introducing an independent model. Direct removals contribute their total weight without shifting the discrepancy; the normalized skew operator retains the actual skew-removal length shifts. Pairing the two positive-count patterns gives the coefficient B^(2r+1)(1+B) at U(r+1,e).")),
                    Paragraph(Text("The identity holds at every integer discrepancy. It is an exact extended-nonnegative-real series, not a truncation error estimate, a nonlinear occupied-mass comparison, or a statement about marginal discrepancy tails. It is not by itself a conditional probability statement on past cylinders."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("endpoint-hazard-definition-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Apply(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);

    private static Formula Statement()
    {
        var e = F.Id("e");
        var r = F.Id("r");
        var b = F.Id("B");
        var coeff = Mul(new Formula.Power(b, Add(Mul(D(2), r), D(1))), Add(D(1), b));
        var term = Mul(coeff, Apply("U", Add(r, D(1)), e));
        var series = Seq(Sum, Underscore, Grp(r, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N"))),
            Sp, Open, term, Close);
        var rhs = Add(Apply("ofReal", Apply("O", e)), series);
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("e"),
            Seq(Mathbb, Grp(F.Id("Z"))),
            new Formula.Relation(Apply("H", e), FormulaRelationOperator.Equal, rhs));
    }
}
