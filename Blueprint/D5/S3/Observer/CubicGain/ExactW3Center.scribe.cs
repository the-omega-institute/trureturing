using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class ExactW3CenterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An algebraic critical-root lift in original parent coordinates",
        H("ExactW3Center"),
        Blocks(
        Paragraph(Text("criticalPolynomial is the degree-67 real polynomial with the descending FC integer coefficient list. It has a unique real root b3 in the open interval (12758053/100000000,12758054/100000000). criticalRoot denotes this root, not a rounded coordinate. The derivative is strictly negative throughout the closed isolating interval. Opposite endpoint signs and the intermediate value theorem give existence; strict decrease gives uniqueness.")),
        Paragraph(Text("A narrower exact enclosure is 127580539798972/1000000000000000 < b3 < 127580539798973/1000000000000000. Polynomial bounds are proved by Horner recurrence. At each recurrence the lower and upper endpoints bound both products with the interval endpoints; induction preserves the enclosure. All coefficient arithmetic and endpoint comparisons use exact integers and rationals.")),
        Paragraph(Text("determinantalLiftDenominator and determinantalLiftNumerator are explicit integer coefficient arrays for the reduced linear-subresultant lift. Set r(b)=-determinantalLiftNumerator(b)/determinantalLiftDenominator(b), and liftedCoordinates(b)=(r(b)/b,b). exactW3 is chartWorld(liftedCoordinates(b3)), expressed in ordinary cubic coefficients.")),
        Paragraph(Text("The denominator is positive on the narrower interval, and the quotient satisfies 9005/10000 <= r(b3) <= 9006/10000. Also 12758/100000 <= b3 <= 12759/100000. These are proved bounds, so SourceCertificate imposes no additional assumption in exactW3_parent. The genuine independent coordinates are (t,b) with t=r/b; no bound t<1 is used.")),
        Paragraph(Text("The chart reconstructs one whole gain polynomial and drift from the literal parent history. Consequently this algebraic lift is an OriginalParent. chartWorld, the original eight-coordinate chartSource, and chartRead=(originalResponse.first,futureRead at the empty common word) are analytic at its lifted coordinates. Every OriginalParent with the same r and b equals this world, including lower degree polynomials and zero samples permitted by the original model.")),
        Paragraph(Text("The regular whole-world correspondence identifies the reconstructed world with the Ck/D lift at these same source coordinates. Identification of the explicit coefficient arrays with the fixed determinant definition remains a separate algebraic obligation. Thus this construction alone does not identify the world with a determinantal critical center. The parent and analyticity conclusions here alone supply neither the remote branch nor exhaustion of the original preimage.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-critical-root-exists"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ExactW3Center.critical_root_exists"),
            H("exact degree-67 critical root"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("criticalPolynomial has degree 67. There exists a real b strictly between rootLo=12758053/100000000 and rootHi=12758054/100000000 with criticalPolynomial.eval(b)=0."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-critical-root-spec"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ExactW3Center.criticalRoot_spec"),
            H("selected root specification"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The selected real criticalRoot satisfies rootLo<criticalRoot, criticalRoot<rootHi and criticalPolynomial.eval(criticalRoot)=0. No parameter or hypothesis is required."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-exact-w3-parent"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ExactW3Center.exactW3_parent_of_source_certificate"),
            H("parent lift from rational strip conditions"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For h:SourceCertificate, OriginalParent exactW3 and AnalyticAt Real chartRead (liftedCoordinates criticalRoot) hold. SourceCertificate is the conjunction of the two rational r bounds, the two rational b bounds and nonvanishing of the determinantalLiftDenominator at criticalRoot."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-exact-algebraic-parent"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ExactW3Center.exactW3_parent"),
            H("unconditional algebraic parent lift"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("With no hypotheses, SourceCertificate and OriginalParent exactW3 hold, and chartWorld, chartSource and chartRead are analytic at liftedCoordinates criticalRoot. For every real b in the original open isolating interval, criticalPolynomial.eval(b)=0 implies b=criticalRoot. For every W:OriginalWorld, OriginalParent W, W.first=liftedR criticalRoot and W.second.first=criticalRoot imply W=exactW3."))),
            DescribeRole.Theorem))));
}
