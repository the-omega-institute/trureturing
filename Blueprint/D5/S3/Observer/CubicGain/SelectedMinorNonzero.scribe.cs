using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class SelectedMinorNonzeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonvanishing of the selected literal leading minor",
        H("SelectedMinorNonzero"),
        Blocks(
        Paragraph(Text("The matrix retains the twenty-eight shifted sourceE0/sourceE1 rows in their original order. Its columns are r^28 through r. Thus its determinant is precisely a0 of the fixed-column prescription, including its sign.")),
        Paragraph(Text("An exact FC sign calculation places criticalRoot between 1275805397989720295463228680851631265311/10^40 and the next rational with denominator 10^40. A rational preconditioner with denominator 2^64 has entries bounded in absolute value by 2^79. At the lower endpoint every entry of its product with the literal matrix differs from the identity by at most 1/128.")),
        Paragraph(Text("On the real unit interval, every matrix entry has Lipschitz constant at most 2^35. Moving from the rational endpoint to criticalRoot changes each preconditioned entry by at most 1/128. The resulting error from the identity is at most 1/64 in each entry. Each diagonal entry therefore has absolute value at least 63/64, while the sum of the other twenty-seven absolute values is at most 27/64. Strict diagonal dominance proves that the product, and hence the chosen literal minor, has nonzero determinant.")),
        Paragraph(Text("This argument concerns the original algebraic root and the actual chosen matrix. It does not infer nonvanishing from uniqueness of a common root. The universal complex-root statements and the full original coefficient-world and response-center identifications require further arguments.")),
        Paragraph(Text("The polynomials literalA0 and literalC0 are the original fixed determinants in Q[b]. Their rational gcd is cleared of denominators, divided by its integer content, and given positive leading coefficient to obtain primitiveGcd. The exact quotients normalizedA=literalA0/primitiveGcd and normalizedC=literalC0/primitiveGcd have integer coefficients. At criticalRoot, primitiveGcd and normalizedA are nonzero. Cancelling their factors in the literal determinant relation identifies -normalizedC/normalizedA with liftedR at this same algebraic root. Both literal sourceE polynomials retain degree fifteen there.")),
        Paragraph(Text("This identifies the selected value of the actual normalized determinant ratio. It does not identify the entire normalized coefficient arrays with the candidate arrays, prove the displayed global factorization or degree of the primitive gcd, or establish the universal complex-root law.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-literal-r-determinant-polynomial"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SelectedMinorNonzero.literalA0"),
            H("original leading determinant polynomial"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The rational polynomial determinant of the twenty-eight shifted source rows, retaining the columns r^28 through r in their original order. Its real evaluation is the determinant of fixedMinorR(literalMatrix(b))."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-literal-constant-determinant-polynomial"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SelectedMinorNonzero.literalC0"),
            H("original constant determinant polynomial"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The rational polynomial determinant of the same rows, retaining columns r^28 through r^2 and then the constant column, in that order. Its real evaluation is the determinant of fixedMinorC(literalMatrix(b))."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-primitive-determinant-gcd"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SelectedMinorNonzero.primitiveGcd"),
            H("positive primitive determinant gcd"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The positive primitive integer associate of the rational polynomial gcd of literalA0 and literalC0. It is formed from the actual determinants."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-normalized-a"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SelectedMinorNonzero.normalizedA"),
            H("actual normalized leading coefficient"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The polynomial quotient literalA0/primitiveGcd in Q[b]. The selected normalized lift theorem proves exact division and integer coefficients."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-normalized-c"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SelectedMinorNonzero.normalizedC"),
            H("actual normalized constant coefficient"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The polynomial quotient literalC0/primitiveGcd in Q[b]. The selected normalized lift theorem proves exact division and integer coefficients."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-selected-normalized-lift"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SelectedMinorNonzero.selected_normalized_lift"),
            H("actual gcd normalization and selected lift"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The actual primitiveGcd is primitive with positive leading coefficient. Its rational image times normalizedA is literalA0, and its rational image times normalizedC is literalC0. At criticalRoot the gcd and normalizedA are nonzero, and -normalizedC/normalizedA equals liftedR. There exist integer polynomials whose rational images are normalizedA and normalizedC. Both literal sourceE0 and sourceE1 have degree fifteen at criticalRoot. No gcd identity, determinant nonvanishing or leading-degree guard is added as a hypothesis."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("cubic-gain-selected-literal-minor-nonzero"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/SelectedMinorNonzero.selected_minor_nonzero"),
            H("nonzero chosen minor at the selected FC root"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The determinant of fixedMinorR(literalMatrix(criticalRoot)) is nonzero. This statement has no additional hypotheses; all matrix entries and the selected FC root are the original ones."))),
            DescribeRole.Theorem))));
}
