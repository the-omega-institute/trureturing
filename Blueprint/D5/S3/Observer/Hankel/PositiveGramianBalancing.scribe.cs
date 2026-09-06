using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class PositiveGramianBalancingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive definite Gramians produce mutually inverse balancing coordinates and an exact Gramian-product spectrum.",
        H("Positive Gramian Balancing"),
        Blocks(
            Describe.Lean(DescribeId.Create("coordinates-type"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.Coordinates"), H("Balancing output"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The output certificate contains the coordinate matrices, positive weights, both inverse identities and both Gramian congruences. Its inhabitation is proved from positive definiteness below."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gramian-root"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot"), H("Positive square root"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uses Mathlib's positive continuous-functional-calculus square root."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gramian-root-spec"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.gramianRoot_spec"), H("Root properties"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derives positive definiteness, self-adjointness and the exact square identity for the constructed root."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinates-nonempty"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates_nonempty"), H("Construction of balancing coordinates"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Diagonalizes sqrt(P) Q sqrt(P) using Mathlib's spectral theorem, rescales by fourth roots, and proves both inverse identities and simultaneous congruences. No balancing matrix is an input. This construction is noncomputable and permits repeated eigenvalues."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coordinates"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.coordinates"), H("Chosen constructed coordinates"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Selects the output of the proved existence construction. This is an exact mathematical construction, not a floating-point eigensolver."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("controllability-factor"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.Coordinates.controllability_factor"), H("Original Gramian reconstruction"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Recovers the original controllability Gramian from the balanced diagonal and inverse coordinate transformation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gramian-product-charpoly"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/PositiveGramianBalancing.Coordinates.gramian_product_charpoly"), H("Gramian-product spectrum with multiplicity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves similarity of the Gramian product to the diagonal of squared balancing weights and derives its full characteristic polynomial. The generally nonsymmetric product is never treated as Hermitian."))), DescribeRole.Theorem)),
        []));
}
