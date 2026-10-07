using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class WindowR2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Window R2"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate window r2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "mR2", "m R2",
                "The weakest eigenvalue bound the far band can use: a0C n − 1/2.", DescribeRole.Definition),
            Node("claim-2", "mR2_ge", "m R2 ge",
                "window_small at the generic reach, now le_refl.", DescribeRole.Theorem),
            Node("claim-3", "a0C_le_one_add", "a0C le one add",
                "a0C n ≤ 1 + 3/n.", DescribeRole.Theorem),
            Node("claim-6", "mAt_ge_mR2", "m At ge m R2",
                "For every admissible contact threshold, the state lower bound dominates the fixed lower bound used to define the enlarged reach window.", DescribeRole.Theorem),
            Node("claim-7", "YR2", "YR2",
                "YR2 n·√T = a0C n − mR2 n = 1/2, identically in t.", DescribeRole.Definition),
            Node("claim-8", "reachNum2", "reach Num2",
                "The generic reach window's numerator: windowR2 α n = reachNum2 n/α + √n/2 by rfl.", DescribeRole.Definition),
            Node("claim-9", "windowR2", "window R2",
                "The generic reach window.", DescribeRole.Definition),
            Node("claim-12", "reachNum2_eq", "reach Num2 eq",
                "reachNum2 = 1/√(mR2).", DescribeRole.Theorem),
            Node("claim-14", "windowR2_lt_p", "window R2 lt p",
                "window_lt_p at the generic reach: 2·reachNum2 n ≤ α·p and α·√n ≤ 1 give windowR2 α n < p. reachNum2 ≈ √2, so the hypothesis is 2.829 ≤ α·p.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
