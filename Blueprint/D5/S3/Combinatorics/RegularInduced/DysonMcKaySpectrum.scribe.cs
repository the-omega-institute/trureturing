using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RegularInduced;

internal sealed class DysonMcKaySpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RegularInduced/DysonMcKaySpectrum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/dyson2026regularinduced");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The regular cyclic bag counts have exactly a clique-packet branch and a period-three full-support branch.",
        H("The cyclic order spectrum"),
        Blocks(
            Node("dyson-mckay-cyclic-order-spectrum", "The exact spectrum of bounded cyclic counts", "cyclic_order_spectrum",
                "Let r be at least four and q be positive. For cyclic positions i, choose nonnegative counts x_i at most s, of total m, satisfying x_{i-1}+x_i+x_{i+1} = q at every occupied position. Such counts exist exactly in either of two cases. In the packet case, m = kq for a nonnegative integer k, with 2k at most r; if q exceeds s then 3k is at most r, and if q exceeds 2s then k = 0. Packets occupy one bag when q is at most s, or two consecutive bags when q is at most 2s, with empty bags separating them. In the full-support case, 3m = rq, q is between three and 3s, and three divides r or q. Subtracting consecutive regularity equations forces the occupied counts to have period three. Positive triples summing to q give the full-support selections when three divides r; constant counts give them when three divides q. The packet branch includes the empty selection.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
