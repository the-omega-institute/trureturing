using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class ProfileBound2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Profile Bound2"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate profile bound2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "mul_exp_three_quarter_le", "mul exp three quarter le",
                "x·e^{3x/4 − x²/8} ≤ e⁶. One completed square, (x−7)² + 7 ≥ 0, after log x ≤ x − 1. The sharp constant is e^{2.39}; nothing downstream cares.", DescribeRole.Theorem),
            Node("claim-2", "rpow_neg_le_of_le", "rpow neg le of le",
                "Monotonicity of (1 − s)^{−c} in s: a larger subtraction gives a larger power.", DescribeRole.Theorem),
            Node("claim-4", "integrableOn_gauss_div_Ioc", "integrable On gauss div Ioc",
                "Integrability of the shifted Gaussian over y on Ioc A B, A > 0.", DescribeRole.Theorem),
            Node("claim-5", "gaussian_over_y_crude", "gaussian over y crude",
                "The crude Gaussian bound. ∫_A^B e^{−(y−b)²/2}/y dy ≤ √(2π)/A: no split, just 1/y ≤ 1/A and the total mass.", DescribeRole.Theorem),
            Node("claim-6", "piece_le", "piece le",
                "The one-dimensional contact integral on an interval (A,B] has the stated Gaussian upper bound whenever A is at least one.", DescribeRole.Theorem),
            Node("claim-7", "I3_le", "I3 le",
                "I₃ with its prefactor. b ≤ 2A makes the constant 2·e^J, with no n and no t outside the exponential.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
