using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class OverlapPerturbationBudgetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/OverlapPerturbationBudget";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nested common-count thresholds bound the total weight divided by Euclidean scales.",
        H("A Diagonal Bound for the Sum of Inverse Scales"),
        Blocks(
            Paragraph(Text(
                "On a finite set J, let w(j)≥0 and |r(j)|≥ρ>0. Write W for the sum of the "
                + "weights and c(m) for the weighted multinomial coefficient of m. For a natural "
                + "degree p, write I(p) for the sum of c(m)c(n)/√S(m,n) over distinct "
                + "ordered pairs of degree p, where S(m,n)=Σ((m(j)−n(j))r(j))². Define "
                + "D(k) as the sum of c(l)² over degree k and A(k)=choose(p,k)² W^(2(p−k))D(k). "
                + "Put T=W^(2p), Q(h)=1/(ρ√(2(p−h))) for h<p with Q(h)=0 for h≥p, and "
                + "B(h)=min over 0≤i≤h of min(A(i),T), minus D(p). "
                + "The correction sum is empty for p≤1. At p=0 the result is zero.")),
            Describe.Lean(
                DescribeId.Create("weighted-inverse-scale-le-of-overlap"),
                DeclarationHandle.Create(Owner + ".weighted_inverse_scale_le_of_overlap"),
                H("The inverse-scale sum is bounded using the lower-degree diagonals"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Distinct equal-degree vectors have common count H<p and "
                        + "reciprocal scale at most Q(H). Split Q(H) into Q(0) and its "
                        + "increments up to H. The increment Q(h+1)−Q(h) is charged "
                        + "exactly on the pairs with H≥h+1. Each earlier threshold bounds "
                        + "this nested tail, so take their minimum and subtract the diagonal. "
                        + "All the increments used by the sum are nonnegative.")),
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
        var h = F.Id("h");
        var next = Add(h, D(1));
        var baseline = Multiply(Seq(Open, F.Id("T"), Minus, Call("D", p), Close), Call("Q", D(0)));
        var index = Seq(D(0), Le, Sp, h, Lt, p, Minus, D(1));
        var difference = Seq(Open, Call("Q", next), Minus, Call("Q", h), Close);
        var correction = Seq(new Formula.Subscript(Sum, index), Sp,
            Multiply(Call("B", next), difference));
        return Disp(AtMost(Call("I", p), Add(baseline, correction)));
    }
}
