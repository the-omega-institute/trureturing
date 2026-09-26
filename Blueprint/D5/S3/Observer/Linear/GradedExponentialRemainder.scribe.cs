using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GradedExponentialRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Obtain the uniform first-order rescaled observation error from the actual Banach-algebra exponential, rather than assuming a Taylor estimate.",
        H("Uniform Graded Exponential Remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exponential-uniform-remainder"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GradedExponentialRemainder.exponential_uniform_remainder"),
                H("Convergent exponential remainder on a norm ball"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uses the pinned exponential power series and its uniform geometric approximation theorem, with radius infinity. The displayed Taylor polynomial uses the actual generator powers and factorial coefficients."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observed-taylor-first"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GradedExponentialRemainder.observed_taylor_first"),
                H("Construct the first visible derivative term"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A readout that annihilates lower generator powers sends the actual Taylor polynomial to the first visible term. The derivative coefficient is calculated from the generator."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-scaled-derivative-layer"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GradedExponentialRemainder.uniform_scaled_derivative_layer"),
                H("Uniform rescaled-time bound after derivative-order normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derives a fixed K such that the error is at most K T uniformly for s in [0,1], for every positive T with T norm(B) below one. Neither a remainder bound nor a Gramian asymptotic is an input hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("explicit-window-radius"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GradedExponentialRemainder.explicit_window_radius"),
                H("Every generator has a nonempty admissible window"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive radius 1/(norm(B)+1) ensures the small-time hypotheses are satisfiable. Integration, graded projection assembly and ordered-eigenvalue asymptotics remain separate obligations."))), DescribeRole.Theorem))));
}
