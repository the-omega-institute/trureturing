using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class ExpDecay99Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Exp Decay99"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate exp decay99 to the stochastic ellipsoid construction.")),
            Node("claim-1", "pow_div_le_exp", "pow div le exp",
                "(x/20)^20 ≤ exp x for x ≥ 0. Real.add_one_le_exp at x/20, then pow_le_pow_left₀; exp x = (exp (x/20))^20 is Real.exp_nat_mul.", DescribeRole.Theorem),
            Node("claim-2", "exp_neg_le", "exp neg le",
                "e^{-x} ≤ 20²⁰/x²⁰ for x > 0 — the decay FailTotalBound99 consumes.", DescribeRole.Theorem),
            Node("claim-3", "exp_neg_nat_le", "exp neg nat le",
                "The form the failure bound uses: at a natural n ≥ 1.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
