using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class ShortfallBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/ShortfallBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Shortfall Bound"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate shortfall bound to the stochastic ellipsoid construction.")),
            Node("claim-1", "pos_part_le_sq_add", "pos part le sq add",
                "u⁺ ≤ u²/(4t) + t for t > 0, every real u. At u > 0 it is (u − 2t)² ≥ 0.", DescribeRole.Theorem),
            Node("claim-2", "pos_part_sub_le_sq", "pos part sub le sq",
                "(u − t)⁺ ≤ u²/(4t) for t > 0, every real u. The shifted form, with no additive t left over: it is what the drift's excess uses, where the shift is already paid for inside L.", DescribeRole.Theorem),
            Node("claim-3", "pos_part_shortfall_le", "pos part shortfall le",
                "The shortfall splits along a pathwise lower bound. No integrability and no measurability: this is an inequality of functions.", DescribeRole.Theorem),
            Node("claim-4", "integral_shortfall_le", "integral shortfall le",
                "The shortfall bound. a closes the martingale half, b the drift-excess half.", DescribeRole.Theorem),
            Node("claim-5", "integral_neg_part_le", "integral neg part le",
                "The martingale half: E[(−M)⁺] ≤ v/(4t) + t from E[M²] ≤ v alone — no mean-zero hypothesis, no tail, no Cauchy–Schwarz. At the chain v = varBound n c₃ ≈ 1.4·10⁻⁴, so t = 0.01 gives 0.0135 and t = √v/2 gives √v ≈ 0.012.", DescribeRole.Theorem),
            Node("claim-6", "integral_drift_excess_le", "integral drift excess le",
                "The drift-excess half: E[(D − dbar)⁺] ≤ w/(4s) where dbar sits s above the centre and w bounds the centred second moment. The chain's D is κ·∑‖π_kξ_k‖², whose centre is κ·h·E[∑ rank π_k] and whose excess over κ·T·dim is bounded by the light-contact budget.", DescribeRole.Theorem),
            Node("claim-7", "shortfall_le", "shortfall le",
                "hshort, assembled. L = c − (cen + s) − t, and the shortfall is v/(4t') + t' + w/(4s) with t' free. Every input is a second moment of a *centred* quantity; nothing here needs the mean of X, the lower tail of X, or Chebyshev.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
