using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileBound7Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile Bound7"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile bound7 to the stochastic ellipsoid construction.")),
            Node("claim-1", "one_le_log_of_three", "one le log of three",
                "log n ≥ 1 for n ≥ 3, because e < 3. This is n₁.", DescribeRole.Theorem),
            Node("claim-2", "drift_eq", "drift eq",
                "The drift is 2√(log n) exactly at T = 16·log n/n².", DescribeRole.Theorem),
            Node("claim-3", "one_le_sqrt_log", "one le sqrt log",
                "√(log n) ≥ 1 for n ≥ 3.", DescribeRole.Theorem),
            Node("claim-4", "window_mul_le", "window mul le",
                "From √t·Y ≤ 1/2 and 0 ≤ y ≤ Y: the window's basic inequality.", DescribeRole.Theorem),
            Node("claim-5", "window_one_sub_pos", "window one sub pos",
                "hpos : 0 < 1 − √t·y on the window.", DescribeRole.Theorem),
            Node("claim-6", "window_gap", "window gap",
                "hSc : 0 < a₀ − √t·y on the window, and shape 4's gap: a₀ − 1/2 ≤ a₀ − √t·y, so the Jacobian bound of substDeriv_le applies with ε = a₀ − 1/2.", DescribeRole.Theorem),
            Node("claim-8", "radiusOf_nonneg", "radius Of nonneg",
                "hρ : 0 ≤ radiusOf 0 — the shell's inner radius is positive.", DescribeRole.Theorem),
            Node("claim-9", "radiusOf_le_end", "radius Of le end",
                "hρW : radiusOf 0 ≤ radiusOf Y and hW : radiusOf y ≤ radiusOf Y — monotonicity.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
