using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class RobinMarginModulusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/RobinMarginModulus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local interpolation of the Robin margin at strict price records",
        H("From the optimizer comparison to the canonical cell bound"),
        Blocks(
            Paragraph(Text("For a real parameter u>1, price(u)=1/(u log u), integerAt(u) is the strict optimizer at that price, and clock(u)=log(integerAt(u)). The Robin log margin at n is EulerGamma+log(log(log n))-log(sigma(n)/n).")),
            Result("robin-margin-increment-bounds", "robin_margin_sub_bounds",
                "Two bounds for the signed margin increment",
                "For 1<u<=v and clock(u)>1, the change in margin from integerAt(u) to integerAt(v) lies between (price(clock(v))-price(u)) times the clock increment and (price(clock(u))-price(v)) times that same increment. Compare the two optimizers at each other's prices to bound the change in the logarithmic divisor ratio. Apply the tangent inequality for log(log x) at each endpoint clock to bound the other term."),
            Result("robin-margin-price-modulus", "robin_margin_modulus",
                "A bound in terms of the two crossed distances",
                "Take a common lower bound a>1 for u and clock(u), with log(a)>=1 and u<=v. If both |clock(v)-u| and |clock(u)-v| are at most D, the absolute margin increment is at most 2D/(a^2 log a) times the clock increment. Monotonicity of the clock places all four price arguments above a, so PolynomialMeshBounds.price_gap bounds each price difference in absolute value."),
            Result("robin-margin-short-step", "robin_margin_local_power_bound",
                "A short step with a power bound for the clock discrepancy",
                "Suppose X>=8, X<=u<=v, v-u<=2, and clock(u)>=X/2. If both parameter-to-clock discrepancies are bounded by C X^beta with beta>=0, each crossed distance is at most (C+2) X^beta. Taking a=X/2 gives the coefficient 16(C+2) X^(beta-2)/log X multiplying the actual clock increment."),
            Result("robin-margin-indexed-cell", "robin_margin_cell_power_bound",
                "The short-step estimate telescopes across a cell",
                "Use the same X, C and beta at every indexed point t(k) between i and j. Each point is at least X, its clock is at least X/2, and its discrepancy is at most C X^beta. If consecutive parameters are nondecreasing with steps at most two, the triangle inequality sums the short-step estimates. The intervening clock increments telescope to clock(t(j))-clock(t(i)), including steps where the strict integer repeats."),
            Result("strict-record-clock-increment", "clock_sub_le",
                "A local arithmetic bound for the strict record clock",
                "A single A>0 works for every 2<=u<=v. The change in clock is at most (v-u+1) log v+A(sqrt u+sqrt v). The von Mangoldt sum from floor(u)+1 to floor(v) has at most v-u+1 terms, each bounded by log v. The strict inventory estimate compares the clock with the Chebyshev function at the two endpoints, adding one square-root error at each endpoint."),
            Result("canonical-robin-margin-cell-bound", "canonical_robin_margin_cell_bound",
                "The cell bound for the literal canonical strict integers",
                "A single A>0 works for every i<=j, X>=8, and C,beta>=0 with the stated cutoff and discrepancy bounds. At each k in the cell, t(k) is in [k+1,k+3/2] and price(t(k)) equals firstLayerPrice(k+1). The windows give ordered consecutive parameters with steps at most two. The price equalities identify the endpoint integers exactly as strictInteger(firstLayerPrice(k+1)). Combining the telescoped bound with clock_sub_le bounds the absolute canonical margin difference by 16(C+2) X^(beta-2)/log X times ((t(j)-t(i)+1) log(t(j))+A(sqrt(t(i))+sqrt(t(j))).",
                "In a power-saving mesh cell with cutoffs comparable to X and width O(X^(1-eta)), this gives a margin error of order O(X^(beta-1-min(eta,1/2))) once the uniform clock hypotheses hold. If beta-min(eta,1/2)<sigma, the error is little-o of X^(sigma-1)/log X. A signed canonical sample of magnitude at least a fixed positive multiple of that scale then keeps its sign at the mesh endpoint, for either sign. The cell estimate supplies the arithmetic comparison used in that transfer."))));

    private static DocumentBlock.Describe Result(string id, string name, string title, params string[] paragraphs) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(paragraphs.Select(prose => Paragraph(Text(prose))).ToArray()), DescribeRole.Theorem);
}
