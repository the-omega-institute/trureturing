using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class ReducedDegreeCollisionBudgetsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/ReducedDegreeCollisionBudgets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separation of low-degree disjoint pairs sharpens the weighted collision budget.",
        H("Collision Budgets from Separation after Cancellation"),
        Blocks(
            Paragraph(Text(
                "Let J be finite. Use nonnegative weights w(j), radii r(j)≥ρ>0, "
                + "a base spectrum g, and a closed window at resolution e. Write B(p) for "
                + "the localized excess budget over ordered distinct degree-p pairs, W for "
                + "the sum of the weights, and D(p) for the degree-p diagonal mass. Set "
                + "C=exp(1/2)√(15π/2). The function ofReal maps a real value to its nonnegative part. Fix a positive integer k. When e>0, for each pair u,v of "
                + "disjoint supports and common degree 0<d<k with d≤p, require the absolute "
                + "gap between their base frequencies to exceed e+Σ(u(j)+v(j))r(j).")),
            Describe.Lean(
                DescribeId.Create("localized-excess-le-of-reduced-separation"),
                DeclarationHandle.Create(Owner + ".localized_excess_le_of_reduced_separation"),
                H("Separated residual pairs below degree k contribute zero"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a pair m,n, subtract their coordinatewise minimum from both "
                        + "vectors. The signed frequency difference is preserved. The "
                        + "residuals have disjoint supports, so their coordinate sum equals "
                        + "the original absolute differences and gives the same drift bound. "
                        + "A reachable distinct pair therefore has reduced degree at least k "
                        + "and Euclidean scale at least ρ√(2k). The multinomial theorem gives "
                        + "the distinct-pair mass W^(2p)−D(p).")),
                    Paragraph(Text(
                        "When e≤0 the localized budget vanishes. At k=1 the separation hypothesis is vacuous. When k>p, every "
                        + "distinct pair is excluded. The premise is a positive-resolution "
                        + "arithmetic condition on the base spectrum. Its validity for the "
                        + "fixed zeta ordinates at the missing-window parameters is open."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Bound()
    {
        var p = F.Id("p");
        var k = F.Id("k");
        var budget = Call("B", p);
        var offDiagonal = Seq(Open, new Formula.Power(F.Id("W"), Multiply(D(2), p)),
            Minus, Call("D", p), Close);
        var probability = Call("min", Call("min", D(1), new Formula.Fraction(F.Id("e"), Rho)),
            new Formula.Fraction(Multiply(F.Id("C"), F.Id("e")), Multiply(Rho, Call("sqrt", Multiply(D(2), k)))));
        var nonpositive = AtMost(F.Id("e"), D(0));
        var beyondDegree = new Formula.Relation(p, FormulaRelationOperator.LessThan, k);
        var outside = Seq(Open, new Formula.Logic(nonpositive, FormulaLogicOperator.Or, beyondDegree), Close);
        var zero = new Formula.Relation(budget, FormulaRelationOperator.Equal, D(0));
        var exact = new Formula.Logic(outside, FormulaLogicOperator.Implies, zero);
        return Disp(new Formula.Logic(Seq(Open, exact, Close), FormulaLogicOperator.And,
            AtMost(budget, Call("ofReal", Multiply(offDiagonal, probability)))));
    }
}
