using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicParityLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicParityLimit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scaled difference between the lattice and cyclic minima has an exact limit on each parity.",
        H("Parity correction for the cyclic minimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-two-cosine-parity-limit"),
            DeclarationHandle.Create(Owner + ".cyclic_parity_correction"),
            H("The gap on the even and odd moduli"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix any positive budget λ and put m=λ/(8π²). The activation data have positive " +
                    "index n with (n²−1)/5≤m<n(n+2)/5. The normalized law is w(j)=(t−j²)₊/Z. " +
                    "Its squared mass is L(m) and its fourth moment is m₄=Σ j⁴w(j).")),
                Paragraph(Text(
                    "Write q=2k+2 on the even sequence, where d=0, and q=2k+1 on the odd sequence, " +
                    "where d=1/2. The feasible weights have first and second cosine moments at least " +
                    "1−λ/q². On each sequence a minimizer exists for all sufficiently large k. The " +
                    "displayed limit means that for each positive tolerance all minimizers satisfy it " +
                    "within that tolerance for all sufficiently large k.")),
                Paragraph(Text(
                    "Set h=2π/q. The quadratic vanishes at C=−cos(dh). Its other root confines its " +
                    "positive part to a fixed front window for large q. The sixth-order cosine remainder " +
                    "gives the fourth-order deficit expansion on this window and the order-h² " +
                    "change of the quadratic. At a zero of the lattice weight the perturbed squared " +
                    "positive part is bounded by a constant times h⁴.")),
                Paragraph(Text(
                    "The moment equations give transfers δ and μ of order h² with μ/h² tending to " +
                    "3m/4. The center and its nearest neighbors have strictly positive lattice " +
                    "weights for every positive budget. The adjusted probabilities are therefore " +
                    "eventually feasible and saturate both moments. At every site carrying mass the " +
                    "quadratic is nonnegative. The energy exceeds the dual bound by the sum of " +
                    "squared distances to the clipped quadratic, which is bounded by a constant " +
                    "times h⁴. This also gives the limit at each activation threshold."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var q = Call("q", F.Id("k"));
        var d = F.Id("d");
        var m = F.Id("m");
        var t = F.Id("t");
        var z = F.Id("Z");
        var lambda = F.LambdaLower;
        var two = F.D(2);
        var qSquared = new Formula.Power(q, two);
        var threshold = Subtract(F.D(1), new Formula.Fraction(lambda, qSquared));
        var gap = Multiply(qSquared, Subtract(Call("L", m), Call("CyclicMinimum", q, threshold)));
        var antipodal = Multiply(Subtract(t, new Formula.Power(d, two)),
            new Formula.Fraction(Multiply(F.D(3), lambda), F.D(8)));
        var fourth = Multiply(new Formula.Fraction(Multiply(F.D(4), new Formula.Power(F.Pi, two)),
            F.D(3)), new Formula.Subscript(m, F.D(4)));
        var coefficient = Multiply(new Formula.Fraction(two, z), Add(antipodal, fourth));
        var limit = new Formula.Subscript(F.Lim, F.Seq(F.Id("k"), F.Sp, F.To, F.Sp, F.Infty));
        return F.Disp(new Formula.Relation(F.Seq(limit, F.Sp, F.Open, gap, F.Close),
            FormulaRelationOperator.Equal, coefficient));
    }
}
