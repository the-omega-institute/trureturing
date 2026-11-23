using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class OverlapPerturbationBudgetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/OverlapPerturbationBudget";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common-count threshold bounds the total weight divided by Euclidean scales.",
        H("A Diagonal Bound for the Sum of Inverse Scales"),
        Blocks(
            Paragraph(Text(
                "On a finite set J, let w(j)≥0 and r(j)≥ρ>0. Write W for the sum of the "
                + "weights and c(m) for the weighted multinomial coefficient of m. For a natural "
                + "degree p, write I(p) for the sum of c(m)c(n)/√S(m,n) over distinct "
                + "ordered pairs of degree p, where S(m,n)=Σ((m(j)−n(j))r(j))². Define "
                + "D(k) as the sum of c(l)² over degree k and A(k)=choose(p,k)² W^(2(p−k))D(k). "
                + "Put T=W^(2p), L=ρ√(2(p−k+1)), and U=ρ√2.")),
            Describe.Lean(
                DescribeId.Create("weighted-inverse-scale-le-of-overlap"),
                DeclarationHandle.Create(Owner + ".weighted_inverse_scale_le_of_overlap"),
                H("The inverse-scale sum is bounded using a lower-degree diagonal"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Distinct equal-degree vectors have common count H<p, so the "
                        + "Euclidean scale is at least ρ√2. When H<k, it is at least "
                        + "L. Charge 1/L to every distinct pair and add 1/U−1/L only "
                        + "for pairs with H≥k. Their total weight is bounded by both A(k) "
                        + "and T before removing the diagonal of mass D(p). At k=0 the "
                        + "correction applies to every distinct pair, and at k=p the two "
                        + "scale bounds agree.")),
                    Paragraph(Text(
                        "For the finite product of independent uniform interval perturbations, "
                        + "the Euclidean-scale affine bound multiplies each inverse scale by "
                        + "exp(1/2)√(15π/2) times the closed resolution. The corresponding "
                        + "weighted perturbation budget is bounded by the displayed right side "
                        + "times this factor. Fixed zeta ordinates still need an arithmetic "
                        + "bound at positive resolution."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Bound()
    {
        var p = F.Id("p");
        var k = F.Id("k");
        var baselineScale = F.Id("L");
        var minimumScale = F.Id("U");
        var total = F.Id("T");
        var diagonal = Call("D", p);
        var baseline = new Formula.Fraction(Seq(total, Minus, diagonal), baselineScale);
        var highWeight = Seq(Call("min", Call("A", k), total), Minus, diagonal);
        var extraCharge = Seq(new Formula.Fraction(D(1), minimumScale), Minus,
            new Formula.Fraction(D(1), baselineScale));
        var result = Add(baseline, Multiply(Seq(Open, highWeight, Close), Seq(Open, extraCharge, Close)));
        return Disp(new Formula.Logic(AtMost(k, p), FormulaLogicOperator.Implies,
            AtMost(Call("I", p), result)));
    }
}
