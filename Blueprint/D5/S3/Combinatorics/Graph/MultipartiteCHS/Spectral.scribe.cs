using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MultipartiteCHS;

internal sealed class SpectralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal adjacency determinant of a complete multipartite graph.",
        H("Spectral coefficients from part sizes"), Blocks(
            Describe.Lean(DescribeId.Create("multipartite-chs-recurrence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Spectral.chs_eq_recH"),
                H("Equality with the part recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural number of parts r, every family a of natural part sizes, and every degree d, the complete homogeneous symmetric polynomial of degree d in the real adjacency eigenvalues equals recH(a,d). No positivity assumption on the part sizes or parity assumption on d is needed.")),
                    Paragraph(Text("Factor the vertex adjacency matrix through the part-index space. The Weinstein-Aronszajn identity reduces its determinant pencil to the r by r matrix with zero diagonal and entry a(j) off the diagonal. Each principal minor of its negative has determinant (1-j) times the product of its j part sizes: column scaling reduces it to the identity minus the all-ones matrix, and the matrix determinant lemma evaluates the latter.")),
                    Paragraph(Text("The determinant is therefore 1 minus the sum, for j from 2 through r, of (j-1)e_j(a)t^j. Mathlib's Hermitian characteristic-polynomial factorization and polynomial reversal identify it with the product of 1-lambda(i)t. The complete homogeneous generating-series identity from PathCHSNormClosedForm then gives the reciprocal determinant. Comparing coefficients yields H(0)=1 and H(d)=sum over 2<=j<=d of (j-1)e_j(a)H(d-j). Strong induction identifies these coefficients with recH. This is an algebraic identity for the literal adjacency matrix; it is independent of any extremality assertion. The spectral definition is Theorem 1.4 of Chavez et al., Extremal polynomial norms of graphs, arXiv:2311.04689; the complete multipartite branch of their Problem 3 is the application."))),
                DescribeRole.Theorem))));
}
