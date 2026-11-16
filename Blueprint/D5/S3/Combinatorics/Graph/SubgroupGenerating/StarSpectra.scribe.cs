using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubgroupGenerating;

internal sealed class StarSpectraDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/das2026sgb");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual star spectra with multiplicity.", H("StarSpectra"), Blocks(
            Describe.Lean(DescribeId.Create("sgb-starspectra-arrowmatrix"),
                DeclarationHandle.Create(Owner + "arrowMatrix"), H("Constant arrow matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite leaf type alpha with decidable equality, arrowMatrix a b c has central diagonal a, leaf diagonal b, center-to-leaf and leaf-to-center entries c, and zero entries between different leaves. The carrier is Unit disjoint-union alpha."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sgb-starspectra-starvalues"),
                DeclarationHandle.Create(Owner + "starValues"), H("Complete star eigenvalue lists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For zero leaves the multiset is the singleton zero. For r positive leaves, adjacency has sqrt(r), -sqrt(r), and r-1 zeroes; L and Q have 0, r+1, and r-1 ones; CN has 0, r-1, and r-1 copies of -1. The zero and one leaf cases retain all vertices and multiplicities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sgb-starspectra-star-matrix"),
                DeclarationHandle.Create(Owner + "star_matrix"), H("The literal four star matrices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The source matrices of the star centered at inl(()) equal the displayed arrow matrices. Adjacency uses (0,0,1), Laplacian uses (r,1,-1), and the explicitly defined signless matrix uses (r,1,1). CN has a zero center block and the leaf block J-I. The degree and common-neighbor identities count the actual neighbor sets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-starspectra-star-spectrum"),
                DeclarationHandle.Create(Owner + "star_spectrum"), H("Actual star spectra with multiplicity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite leaf type alpha, decidable equality and every matrix kind, the actual Hermitian eigenvalue multiset of the star on Unit disjoint-union alpha is starValues(card(alpha),kind). A Schur-complement determinant identity proves the arrow characteristic polynomial; polynomial cancellation is restricted to positive leaf count. Zero leaves are treated directly. Characteristic roots are identified with the actual Hermitian eigenvalues. These star spectra are known suppliers in Das-Erfanian-Nath, rather than a claim of new literature novelty."))), DescribeRole.Theorem))));
}
