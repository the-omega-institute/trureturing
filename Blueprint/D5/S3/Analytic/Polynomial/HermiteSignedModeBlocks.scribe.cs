using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteSignedModeBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteSignedModeBlocks.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026hermitesignedmode");

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The differences of the signed Hermite mode form blocks (1,1,1,−3) and (1,1,1,1,−3), with "
            + "quadratically spaced long blocks, and the mode grows like √(2n).",
        H("Blocks and growth of the signed Hermite mode"),
        Blocks(
            Def("hermite-blocks-g", "G", "The quadratic G", "G(j) = j² + 5j + 7."),
            Def("hermite-blocks-offset", "blockOffset", "The offset j_r",
                "j_r is the least j with G(j) ≥ 8r; in particular j_0 = 0."),
            Def("hermite-blocks-start", "blockStart", "The block start n_r",
                "n_r = 4r + j_r, so n_0 = 0."),
            Def("hermite-blocks-r", "R", "The long-block indices", "R_j = ⌊G(j)/8⌋."),
            Def("hermite-blocks-alpha", "alpha", "The lower envelope", "α_n = (√(8n + 21) − 7)/2."),
            Describe.Lean(DescribeId.Create("hermite-blocks-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Block description and growth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let a(n) be the signed Hermite mode and q(n) = (n − a(n))/4. Then q(n) ≥ r exactly "
                        + "when n ≥ n_r, and a(n + 1) − a(n) = −3 exactly when n + 1 is a block start n_r; by the "
                        + "frozen HermiteSignedMode result every other difference is 1, so block r occupies the "
                        + "differences n_r, …, n_{r+1} − 1 and ends with −3. The starts satisfy n_0 = 0, n_1 = 5 and "
                        + "n_{r+1} − n_r ∈ {4, 5} for every r; the gap is five exactly when r = R_j for some j "
                        + "(the first block is R_0 = 0), with n_{R_j} = 4R_j + j, and every block strictly between "
                        + "R_j and R_{j+1} has length four. The number R_{j+1} − R_j − 1 of those blocks satisfies "
                        + "−3/4 ≤ R_{j+1} − R_j − 1 − j/4 ≤ 1/4, both ends attained (j = 7 and j = 3). Finally "
                        + "α_n ≤ a(n) < α_n + 4, −7/2 < a(n) − √(2n) < 3 and a(n)/√(2n) → 1.")),
                    Paragraph(Text(
                        "By the quadratic threshold, q(n) ≥ r exactly when 4r ≤ n and G(n − 4r) ≥ 8r, that is "
                        + "n ≥ n_r; since q(n + 1) − q(n) ∈ {0, 1}, the difference a(n + 1) − a(n) = 1 − 4(q(n + 1) "
                        + "− q(n)) is −3 exactly at a block start. As G(j + 1) − G(j) = 2j + 6 ≥ 8 for j ≥ 1, "
                        + "j_{r+1} − j_r ∈ {0, 1}, and j_{r+1} = j_r + 1 exactly when G(j_r) < 8r + 8, that is "
                        + "r = ⌊G(j_r)/8⌋. Conversely j_{R_j} = j, because G is odd and G(j) − G(j − 1) ≥ 8 for "
                        + "j ≥ 2, with R_0 = 0 and R_1 = 1 checked directly. Writing j = 8q + s gives "
                        + "G(8q + s) = 8(8q² + 2qs + 5q) + G(s), and the eight residues s give the count range. The envelope follows from (2a + 7)² ≥ 8n + 21 and, "
                        + "four steps lower in the residue class, (2a − 1)² < 8n + 21, together with "
                        + "2√(2n) < √(8n + 21) ≤ 2√(2n) + 5. This is Corollary 2 of H. Ma and W. Zhang "
                        + "(DOI 10.5281/zenodo.23957586) on the observations of Mike Sheppard in OEIS A381423."))),
                DescribeRole.Theorem))));
}
