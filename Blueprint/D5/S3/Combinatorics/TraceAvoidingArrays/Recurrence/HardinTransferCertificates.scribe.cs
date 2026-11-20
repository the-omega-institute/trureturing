using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinTransferCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source vector identities with exact integer lags.",
        H("Continuation polynomials"),
        Blocks(
            Node("row1", "rowOne", "Full-state relation at height 1", DescribeRole.Theorem,
                "On all three unrestricted columns at height one, the entries of the powers on ones at exponents 0, 1 and 2 are 1, 2 and 4, respectively. Thus C²1 = 3C1 − 2·1. The coefficient sum is one. Multiplying by C gives the manuscript relation at shift one."),
            Node("column4-lags", "wordFourCoefficients", "Source lag coefficients", DescribeRole.Definition,
                "The coefficients at lags one through 3 are (8, −11, 4)."),
            Node("column4", "wordFour", "Full-state relation at width 4", DescribeRole.Theorem,
                "On all 24 proper words at width four, the diagonal transfer power at exponent 3 on ones equals the source lag-weighted sum of the power vectors at exponents 2 down to 0. The coefficient sum is one. For each state, the permitted successors exclude the labels on all incident cross-bonds and require adjacent labels to differ. Horner evaluation gives zero residual at each proper word."),
            new DocumentBlock.Section(H("Consequences of the low-width continuations"), Blocks(
                Paragraph(Text("HardinActualTransfers identifies the powers on ones with the corresponding continuations, including the empty tail at exponent zero. For each of the six proper width-two words, HardinThinGraphTransport.continuation_two, from transition_counts, gives 3^m for both the diagonal and square vertical-bond rules. The vectors at exponents 0, 1 and 2 therefore have entries 1, 3 and 9, and 9=4·3−3·1. The lag list (4, −3) sums to one.")),
                Paragraph(Text("For all twelve proper width-three words and both bond rules, HardinThinGraphTransport.continuation_three uses the same K=[[3,2],[2,2]] on the equal-endpoint and unequal-endpoint classes in that order. The vectors at exponents 0 through 3 are (1,1), (5,4), (23,18), (105,82). In these coordinates v₃=6v₂−7v₁+2v₀, so the identity holds at every original proper word. The lag list (6, −7, 2) sums to one.")),
                Paragraph(Text("For all nine unrestricted height-two columns, HardinColumnContinuations.continuation_B and HardinActualTransfers.column_power give the power vectors via B=[[2,2],[1,0]], in equal-label and unequal-label classes. The vectors at exponents 0 through 4 are (1,1), (4,1), (10,4), (28,10), (76,28). Since v₂=2v₁+2v₀, the quadratic (C²−2C−2I)1 is zero on all nine columns, giving the vector premise for the two-row radical. Since v₃=3v₂−2v₀, the source list (3, 0, −2) holds at shift zero. Applying C gives v₄=3v₃−2v₁. The list sums to one.")),
                Paragraph(Text("For all 27 unrestricted height-three columns, HardinColumnContinuations.continuation_H uses Hfull=[[2,4,2,0],[1,1,0,0],[1,0,0,0],[0,0,0,0]]. The classes in order are all equal, exactly one adjacent equality, endpoints only equal, and all distinct. The last class is isolated, with an empty tail at exponent zero and no continuations at positive exponents. The vectors at exponents 0 through 5 are (1,1,1,1), (8,2,1,0), (26,10,8,0), (108,36,26,0), (412,144,108,0), (1616,556,412,0). The identity v₅=4v₄+v₃−6v₂+2v₁ gives the source relation on all columns. The list (4, 1, −6, 2) sums to one.")),
                Paragraph(Text("The zero shifts concern the three-label vectors. For the literal normalized row counts, the connected-rectangle identity applies only at widths at least two. For height one the counts at widths 1, 2 and 3 are 1, 1 and 3, so the equation with lags (6, −8) fails at width 3. For height two the counts at widths 1 through 4 are 3, 8, 80 and 800, so the equation with lags (12, 0, −128) fails at width 4. The literal recurrences begin at widths 4 and 5 respectively."))))
        )));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
