using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FiniteMultinomialOverlapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FiniteMultinomialOverlap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common subvector bounds weighted overlap through a lower-degree diagonal.",
        H("Common Counts of Weighted Multinomial Vectors"),
        Blocks(
            Paragraph(Text(
                "Let J be finite, let the weights w(j) be nonnegative, and let c(m) be the "
                + "multinomial coefficient times the monomial weight of count vector m. "
                + "Write W for the sum of the weights. For degree p vectors m and n, "
                + "H(m,n) is the sum of their coordinatewise minima. Write D(k) for "
                + "the sum of c(l)² over degree k and A(p,k) for the sum of c(m)c(n) "
                + "over ordered pairs of degree p with H(m,n) at least k.")),
            Describe.Lean(
                DescribeId.Create("weighted-overlap-le-diagonal"),
                DeclarationHandle.Create(Owner + ".weighted_overlap_le_diagonal"),
                H("A lower-degree diagonal bounds large common counts"),
                StatementSource.FromAuthor(OverlapBound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For k≤p, any pair counted by A(p,k) contains a common subvector l of "
                        + "degree k. Count each choice of occurrences of l on each side. The "
                        + "multiplicity is the product of the coordinate binomial coefficients. "
                        + "For fixed l, write m=l+u. The product of the weight c(m) and "
                        + "its subvector multiplicity is choose(p,k)c(l)c(u), by canceling "
                        + "the factorials and factoring the weights coordinate by coordinate. "
                        + "Summing over u gives choose(p,k)c(l)W^(p−k). "
                        + "The two sides sum independently, and the sum over l yields the bound."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the next estimate the weights are immaterial. Given two natural count "
                + "vectors of degree p and radii r(j)≥ρ≥0, write S for the sum of "
                + "((m(j)−n(j))r(j))².")),
            Describe.Lean(
                DescribeId.Create("weighted-count-difference-sq-ge"),
                DeclarationHandle.Create(Owner + ".weighted_count_difference_sq_ge"),
                H("The unmatched count bounds the squared frequency scale"),
                StatementSource.FromAuthor(ScaleBound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The absolute count differences sum to 2(p−H(m,n)) since "
                        + "each side has degree p. Each count difference is an integer, "
                        + "so its square is at least its absolute value. Multiply each "
                        + "comparison by the square of the common radius lower bound and sum."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "In the uniform perturbation model the second estimate bounds the Euclidean "
                + "scale on pairs with small H, and the first controls the weight of pairs "
                + "with large H. The fixed zeta ordinates still require a positive-resolution "
                + "arithmetic bound.")))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula OverlapBound()
    {
        var p = F.Id("p");
        var k = F.Id("k");
        var chooseSquared = new Formula.Power(Call("choose", p, k), D(2));
        var exponent = Multiply(D(2), new Formula.Binary(p, FormulaBinaryOperator.Subtract, k));
        var weightedScale = Multiply(new Formula.Power(F.Id("W"), exponent), Call("D", k));
        return Disp(new Formula.Logic(AtMost(k, p), FormulaLogicOperator.Implies,
            AtMost(Call("A", p, k), Multiply(chooseSquared, weightedScale))));
    }

    private static Formula ScaleBound()
    {
        var unmatched = new Formula.Binary(F.Id("p"), FormulaBinaryOperator.Subtract,
            Call("H", F.Id("m"), F.Id("n")));
        var radiusSquared = new Formula.Power(Rho, D(2));
        return Disp(AtMost(Multiply(Multiply(D(2), radiusSquared), unmatched), F.Id("S")));
    }
}
