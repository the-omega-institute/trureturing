using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class ParamsAdopted2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Params Adopted2"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate params adopted2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "numStepsAdopted2", "num Steps Adopted2",
                "N = ⌈16 n⁷ log n⌉ — the adopted number of steps at h = n⁻⁹.", DescribeRole.Definition),
            Node("claim-2", "stepSizeAdopted2", "step Size Adopted2",
                "h = T / N ≤ n⁻⁹ — the adopted step size.", DescribeRole.Definition),
            Node("claim-3", "numStepsAdopted2_mul_stepSizeAdopted2", "num Steps Adopted2 mul step Size Adopted2",
                "The horizon is hit exactly: N · h = T.", DescribeRole.Theorem),
            Node("claim-6", "eta2_le", "eta2 le",
                "η ≤ √2 · n⁻³ — the per-step threshold √(2 h d n) at h ≤ n⁻⁹, d ≤ n². (Discharge.eta_le gives √2 · n⁻² at h ≤ n⁻⁷.)", DescribeRole.Theorem),
            Node("claim-7", "stepGood_cost2_le", "step Good cost2 le",
                "The union-bound cost at the new N: ≤ 33 n⁹ log n. (Discharge.stepGood_cost_le gives 33 n⁷ log n at N = ⌈16 n⁵ log n⌉.)", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
