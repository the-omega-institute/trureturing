using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class L1BitingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform integrability of literal low restrictions",
        H("Uniform integrability of literal low restrictions"),
        Blocks(
            Describe.Lean(DescribeId.Create("uniformintegrable-complements"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/L1Biting.uniformIntegrable_complements"),
                H("Uniform integrability of literal low restrictions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. Assume mu is finite. Let f be an L1 sequence bounded in norm by a real B, let K be a natural sequence with n < K(n), and let c be a real sequence tending to a real alpha. Suppose every fixed tailNorm(k,f(n)) tends to c(k) and the moving tailNorm(K(n),f(n)) tends to alpha. Then the coerced sequence of literal restrictions of f(n) to the complements of tailSet(K(n),f(n)) is UniformIntegrable at exponent one. Exact nested-tail subtraction gives the late-index bounds. The finite initial family is controlled separately before invoking the hard-tail characterization. No weak convergence is assumed."))), DescribeRole.Theorem))));
}
