using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ReflectedSpectralWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual central-defect evolution has a positive spectral gap and a finite-window endpoint bound.",
        H("Finite-time endpoint average on the central-defect path"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("central-defect-endpoint-average"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/ReflectedSpectralWindow.central_defect_endpoint_average"),
                H("The central-defect endpoint average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Eigenstructure/childs2003gluedtrees")),
                Blocks(
                    Paragraph(Text(
                        "Use a path on 2n vertices with n at least one, zero diagonal, " +
                        "unit nearest-neighbor weights and square-root-two weight on the central edge. " +
                        "Enumerate all the eigenvalues with algebraic multiplicity, and define the " +
                        "gap as the minimum of the absolute differences at distinct indices. " +
                        "This gap is strictly positive.")),
                    Paragraph(Text(
                        "For any positive error parameter, let the time window start at zero and " +
                        "have length at least twice the vertex count divided by the error parameter " +
                        "and the actual gap. The real time average of the squared norm of the " +
                        "entry from vertex zero to vertex 2n minus one of the matrix exponential " +
                        "of the entrywise complexified path matrix multiplied by minus i times the " +
                        "evolution time strictly exceeds " +
                        "the ratio of one minus the error parameter to the vertex count.")),
                    Paragraph(Text(
                        "The estimate formalizes the weighted-path part of Childs et al., " +
                        "Section III.D, Lemma 1. The existing spectral gap theorem gives " +
                        "simple eigenvalues. Coordinate " +
                        "reversal preserves the matrix and each eigenline, so the eigenvectors have " +
                        "equal absolute weights at the endpoints. The exponential acts on these " +
                        "eigenlines by the corresponding phases. The diagonal part of the integrated " +
                        "energy is bounded by Cauchy–Schwarz. Integration of the real cosine terms " +
                        "bounds the remaining interference by its off-diagonal weight."))),
                DescribeRole.Theorem))));
}
