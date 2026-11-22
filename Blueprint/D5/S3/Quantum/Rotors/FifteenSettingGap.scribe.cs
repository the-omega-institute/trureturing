using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Rotors;

internal sealed class FifteenSettingGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Rotors/FifteenSettingGap.";

    private static Formula SqrtTwo() => Seq(Sqrt, Grp(D(2)));
    private static Formula Factor() => new Formula.Power(Seq(Open, D(1), Plus, SqrtTwo(), Close), D(2));
    private static Formula Fraction(Formula n, Formula d) => new Formula.Fraction(n, d);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Thirty comparisons between five base settings and ten pair settings yield a positive error for any finite fixed-weight mixture of four-dimensional unit rotor readings.",
        H("Fifteen settings for a rotor mixture"),
        Blocks(
            Describe.Lean(DescribeId.Create("pair-sum"), DeclarationHandle.Create(Prefix + "pairSum"),
                H("Ten unordered pairs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each unordered pair of the five indices is counted once, by choosing its increasing order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("frame-obstruction"), DeclarationHandle.Create(Prefix + "fifteen_setting_gap"),
                H("Frame energy and the midpoint discrepancy"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("D"), Sp, Ge, Sp, Fraction(D(5), Seq(D(4), Factor()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Five unit vectors in real dimension four have upper off-diagonal Gram energy at least 5/8. Assign any unit vector to each of the ten pairs. The discrepancy D sums the squared distances between each base-vector sum and the assigned pair vector scaled by the square root of two.")),
                    Paragraph(Text("The four-by-four frame operator has trace five. Its squared trace is bounded by four times the trace of its square. Removing the five diagonal squares of the Gram matrix and counting each pair once gives 5/8. The reverse triangle inequality bounds the discrepancy from below even when two base vectors coincide or are antipodal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("half-angle-probability"), DeclarationHandle.Create(Prefix + "comparison"),
                H("Half-angle comparison probability"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite list of fields, this adds one to their weighted mean dot product and divides by two. For nonnegative weights summing to one it equals the weighted mean of the individual probabilities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-mixture-gap"), DeclarationHandle.Create(Prefix + "fixed_mixture_probability_gap"),
                H("A common error bound for thirty comparisons"),
                StatementSource.FromAuthor(Disp(Seq(DeltaLower, Sp, Ge, Sp, Fraction(D(5), Seq(
                    D(8, 0), Factor(), Open, D(2), Plus, D(4), SqrtTwo(), Close))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each finite field assigns a real four-dimensional unit vector to each setting. A single array of nonnegative weights summing to one is used for all settings. Compare the ten base pairs to probability one half and the twenty incident base-to-pair comparisons to (1+1/√2)/2. Every common absolute error bound on those thirty comparisons satisfies the displayed inequality.")),
                    Paragraph(Text("Squaring each midpoint discrepancy expresses it as an affine function of the three dot products. Taking a common weighted mean preserves the lower bound on D. If all thirty probability errors are bounded by delta, the mean discrepancy is at most ten times (4+8√2) times delta."))), DescribeRole.Theorem))));
}
