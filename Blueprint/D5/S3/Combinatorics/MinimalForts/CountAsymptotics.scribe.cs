using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class CountAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/CountAsymptotics.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All finite residues share convergence", H("All finite residues share convergence"),
        Blocks(
            Node("mixed-count-normalization", "Normalization of all actual minimal forts", "mixed_count_normalization", "For each r in Fin 6 and arbitrary natural-valued sequences x,y,z whose sum is k at every index, if the actual signed logarithmic error x log(2/3)+z log(4/3)-k slope-offset(r) tends to zero, then the complete minimal-fort count of MixedBlocks.graph(x(k),y(k),z(k),r), divided by (3/2)^(6k+r+3), tends to one. The count is the cardinality of the entire family of inclusion-minimal nonempty forts of that graph. Its root-containing term is the exponential of the error after normalization. Its nonnegative root-free term is bounded by 15k+choose(r+2,2), and is negligible relative to the exponential denominator. The theorem assumes the sequence error, not a graph count or its asymptotic consequence.", DescribeRole.Theorem),
            Node("finite-diagonal", "All finite residues share convergence", "finite_diagonal", "For every finite type of indices, real limit l, and family f(i,k) tending to l for each index, every index selector a(n) and natural block selector b(n) tending to infinity give f(a(n),b(n)) tending to l along the entire natural sequence. Finiteness supplies one tail bound simultaneously for every index. The selectors need not converge or be monotone.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
