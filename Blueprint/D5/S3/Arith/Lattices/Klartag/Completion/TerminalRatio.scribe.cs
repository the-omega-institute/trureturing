using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class TerminalRatioDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Terminal Ratio"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate terminal ratio to the stochastic ellipsoid construction.")),
            Node("claim-1", "n_mul_pow_mul_C1cR", "n mul pow mul C1c R",
                "ThetaTight.n_mul_pow_mul_C1c at KcR. C1cR differs from C1c only by Kc → KcR, so the same identity holds and the combination is again α-free.", DescribeRole.Theorem),
            Node("claim-2", "alpha_mul_rhoC_pow_le", "alpha mul rho C pow le",
                "(α·ρ)ⁿ ≤ 1 at a₀ = a0C n: √(a0C n) = (1 − 1/n)⁻¹, so α·ρ ≤ 1 − 3/(4n) < 1.", DescribeRole.Theorem),
            Node("claim-3", "thetaTight_terminal_le", "theta Tight terminal le",
                "The terminal threshold is Θ(n²) with an absolute constant. b is the coefficient the combined weight gives the terminal summand (b = 1 for the bare radial bound, b = 4 once ChainRaw3.tailT's own factor is counted).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
