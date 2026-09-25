using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class OscillatorSensorJetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compute the actual derivative rows and exact rational polynomial-Gramian constants for the equal-gain sum and separate sensors; exponential remainder and statistical limit proofs remain separate.",
        H("Two Oscillator Sensor Jets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sum-jet-table"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/OscillatorSensorJets.sum_jet_table"),
                H("Compute the four normalized sum-sensor derivative rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rows are calculated from C B^k/k!, not entered as an observability hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separate-first-derivative"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/OscillatorSensorJets.separate_first_derivative"),
                H("Both hidden momenta appear at derivative order one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed two-row matrix is obtained by multiplying the separate position sensor by the actual two-frequency generator."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-initial-gain"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/OscillatorSensorJets.equal_initial_gain"),
                H("The sensor comparison uses equal total squared gain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both C-transpose times C trace values are exactly two."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sum-jets-observable"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/OscillatorSensorJets.sum_jets_observable"),
                H("An explicit inverse recovers the four-dimensional state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse matrix is constructed and multiplied against the derived jet table, proving that the joint derivative kernel is zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sum-polynomial-gram-determinant"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/OscillatorSensorJets.sum_polynomial_gram_determinant"),
                H("Exact sum-sensor polynomial determinant constant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient is exactly 1/2688000, using the derived jet determinant and the rational Hilbert moment determinant. This is not a proof of the exponential Gramian limit."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separate-polynomial-gram-determinant"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/OscillatorSensorJets.separate_polynomial_gram_determinant"),
                H("Exact independent-sensor polynomial determinant constant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient is exactly 1/36 for the two independent leading oscillator blocks."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scaled-sum-polynomial-determinant"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/OscillatorSensorJets.scaled_sum_polynomial_determinant"),
                H("Exact time scaling of the polynomial model"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scaled polynomial Gramian has determinant T^16/2688000 for every rational T, including zero. The exponential trajectory requires an additional remainder proof before this becomes an asymptotic claim."))), DescribeRole.Theorem))));
}
