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
                + "D(k) as the sum of c(l)² over degree k and A(k)=choose(p,k)² W^(2(p−k))D(k).")),
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
                        + "ρ√(2(p−k+1)). Bound the weight of pairs below the threshold "
                        + "by W^(2p) and the weight of pairs at or above it by A(k). Both "
                        + "bounds refer to the same weighted ordered pairs.")),
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
        var remaining = Add(new Formula.Binary(p, FormulaBinaryOperator.Subtract, k), D(1));
        var highScale = Multiply(Rho, Call("sqrt", D(2)));
        var lowScale = Multiply(Rho, Call("sqrt", Multiply(D(2), remaining)));
        var totalWeight = new Formula.Power(F.Id("W"), Multiply(D(2), p));
        var result = Add(new Formula.Fraction(totalWeight, lowScale),
            new Formula.Fraction(Call("A", k), highScale));
        return Disp(new Formula.Logic(AtMost(k, p), FormulaLogicOperator.Implies,
            AtMost(Call("I", p), result)));
    }
}
