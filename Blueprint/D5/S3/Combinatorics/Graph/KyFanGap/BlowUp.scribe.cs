using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class BlowUpDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent-class blow-ups and the limit of normalized graph Ky Fan maxima.",
        H("Blow-ups and asymptotic graph maxima"), Blocks(
            Describe.Lean(DescribeId.Create("blow-up-matrix"),
                DeclarationHandle.Create(Owner + "blowUpMatrix"),
                H("Independent-class blow-up matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The matrix replaces each entry of A by a constant square block of order t. For an adjacency matrix, each vertex is replaced by t independent vertices, and each original edge becomes a complete bipartite graph."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("graph-blow-up-lower"),
                DeclarationHandle.Create(Owner + "kyFan_blowUp_le_xi"),
                H("Blow-up lower bound for a graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("For positive t, the maximum at order mt is at least t times the Ky Fan sum of G. Truncate the prefix at the original dimension when necessary. Repeat each coordinate of an attaining signed orthonormal family t times and divide by sqrt(t). Inner products remain unchanged, and the adjacency operator scales its pairing by t."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("graph-isolated-vertices"),
                DeclarationHandle.Create(Owner + "xi_mono"),
                H("Monotonicity under isolated vertices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("For m at most n, the maximum at order m is no larger than that at order n. Embed the graph, add isolated vertices, and extend every vector of an attaining signed family by zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("graph-max-blow-up"),
                DeclarationHandle.Create(Owner + "xi_blowUp"),
                H("Blow-up lower bound for the maximum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("Taking a graph that attains the finite maximum yields xi(k,mt) at least t times xi(k,m), provided t is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-supremum"),
                DeclarationHandle.Create(Owner + "normalizedSupremum"),
                H("Normalized supremum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("The value is the supremum of xi(k,m)/m over all orders m at least k, expressed by the index m+k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-max-limit"),
                DeclarationHandle.Create(Owner + "tendsto_xi_div"),
                H("Existence and value of the normalized limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("For every positive k, xi(k,n)/n converges to its supremum over orders at least k. The universal zero-one matrix bound bounds this supremum by (1+sqrt(k))/2. For a fixed order m, use floor(n/m) copies of each vertex and fill the remaining positions with isolated vertices. The resulting lower bound is (1-(n mod m)/n) times xi(k,m)/m. The remainder ratio tends to zero. Taking m with normalized maximum above any chosen lower threshold proves the lower limit bound; the supremum gives the upper bound."))),
                DescribeRole.Theorem))));
}
