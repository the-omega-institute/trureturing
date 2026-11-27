using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qGramCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.";
    private static readonly LibraryNoteRef Nebe = LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral Gram matrix in the P48q catalogue basis has an integral inverse and is preserved by the concrete order-three row action.",
        H("The P48q Gram Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nebe-gram"),
                DeclarationHandle.Create(Prefix + "nebeGram"),
                H("The catalogue Gram matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("G is the symmetric integer matrix obtained from the triangular GRAM table in the Nebe–Sloane catalogue’s P48q entry, with both axes indexed by Fin 48."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nebe-gram-inverse"),
                DeclarationHandle.Create(Prefix + "nebeGramInverse"),
                H("The integral inverse table"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The inverse is an explicit integer matrix H in the same basis as G."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nebe-lattice-data"),
                DeclarationHandle.Create(Prefix + "nebeLatticeData"),
                H("The rank-48 lattice data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The rank-48 lattice data uses G as its integral form. The symmetry and evenness of each diagonal entry are checked directly on the table."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("p48q-gram-inverse-certificate"),
                DeclarationHandle.Create(Prefix + "gram_inverse_certificate"),
                H("The inverse product is the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The integral matrices satisfy HG = I. The rowwise integer dot products give HGᵀ = I, and the catalogue Gram matrix is symmetric."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-gram-isometry-certificate"),
                DeclarationHandle.Create(Prefix + "gram_isometry_certificate"),
                H("The order-three action preserves the form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(
                    Paragraph(Text("M is the fourth power of the first catalogue generator, as in the P48q fixed-rank certificate. In the catalogue’s row coordinates the action is x ↦ xM, so preservation of the Gram form is MGMᵀ = G.")),
                    Paragraph(Text("The first rowwise check multiplies M by G and verifies the intermediate table. The second multiplies that table by Mᵀ and recovers G. Both checks use exact integer dot products."))),
                DescribeRole.Theorem))));
}
