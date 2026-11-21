using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9IsotropicSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduction of supported eigenvectors at an eigenvalue divisible by a prime",
        H("Reduction of a supported eigenspace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-spectral-specialization-defect"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicSupport.exists_zmod_kernel_supported_of_real_eigenvector"),
                H("A nonzero real supported eigenvector forces a modular kernel vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Restrict the integer matrix after subtracting the eigenvalue to the columns in the prescribed support. If its reduction were injective, a linear left inverse over the prime field could be lifted to an integer matrix. The square product would have determinant congruent to one and would remain injective over the reals.")),
                    Paragraph(Text("The real eigenvector rules out this injectivity. When the eigenvalue is divisible by the prime, the resulting nonzero modular vector is killed by the original operator and remains supported within the prescribed set."))),
                DescribeRole.Theorem)),
        []));
}
