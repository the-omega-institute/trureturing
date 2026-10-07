using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43UniformRDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43Uniform R"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43uniform r to the stochastic ellipsoid construction.")),
            Node("claim-1", "r16", "r16",
                "n^{1/16}, as four nested square roots.", DescribeRole.Definition),
            Node("claim-6", "junk_endpoint_two_log", "junk endpoint two log",
                "At the doubled logarithmic endpoint and above the dimension threshold, the correction term is at most three. The logarithmic growth is bounded by a sixteenth power of the dimension.", DescribeRole.Theorem),
            Node("claim-7", "pieces_four", "pieces four",
                "The four-piece radial bound. pieces_at_params on (0, Ymid] and FarBand.far_le on (Ymid, Y1], summed. The far band contributes at most 1, so K becomes K + 1.", DescribeRole.Theorem),
            Node("claim-8", "logn_sqrtT_le_quarter", "logn sqrt T le quarter",
                "log n·√T ≤ 1/4 — the quarter version of Lemma43Uniform.logn_sqrtT_le, needed because the split point is 2·log n.", DescribeRole.Theorem),
            Node("claim-9", "twelve_le_log", "twelve le log",
                "12 ≤ log n at the threshold (e¹² = 162 755 ≤ 2 073 600).", DescribeRole.Theorem),
            Node("claim-10", "KcR", "Kc R",
                "pieces_four's constant: Lemma43Uniform.Kc + 1.", DescribeRole.Definition),
            Node("claim-11", "C1cR", "C1c R",
                "Lemma 4.3's per-t constant at the reach window.", DescribeRole.Definition),
            Node("claim-15", "ct_le", "ct le",
                "((n+2)/2)·t ≤ 1/100 for t ≤ T — the far band's a ≥ 0.49.", DescribeRole.Theorem),
            Node("claim-16", "cs_le", "cs le",
                "((n+2)/2)·√t ≤ 3·√(log n) for t ≤ T.", DescribeRole.Theorem),
            Node("claim-17", "far_numerics", "far numerics",
                "The far band's two numeric side conditions, as a standalone lemma: pieces_four's hlam and hfar at the split point Ymid ≥ 2·log n.", DescribeRole.Theorem),
            Node("claim-18", "C1R", "C1R",
                "Lemma 4.3's per-t constant at the reach window, with the small-t branch's e².", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
