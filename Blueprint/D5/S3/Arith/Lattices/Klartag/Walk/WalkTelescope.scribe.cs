using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class WalkTelescopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Walk Telescope"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate walk telescope to the stochastic ellipsoid construction.")),
            Node("claim-2", "padIncVec", "pad Inc Vec",
                "The padding construction's increment vector. The i-th coordinate is the negated padded increment: the martingale difference ΔM_i plus the padding c_i·η_i.", DescribeRole.Definition),
            Node("claim-4", "walkSum_padded_eq", "walk Sum padded eq",
                "walkSum_padded_eq — Padding.padded_tail_of_increments' hincw, proved. The only proviso is that M 0 is the deterministic constant M₀, which is exactly Klartag's initial gap read at time zero.", DescribeRole.Theorem),
            Node("claim-5", "hprop_of_hincl", "hprop of hincl",
                "The transported Proposition 4.1, with hincw discharged. ChainWalk.tail_of_transport'' and ChainWalk.chainRaw2_of_walk take hprop; this is hprop with everything proved except the padded increment vector's law.", DescribeRole.Theorem),
            Node("claim-6", "hitSet_smul", "hit Set smul",
                "The hitting event is scale-invariant. The chain's walk ⟪A_k, q y⟫ − 1 and its normalisation by ‖q y‖ = ‖x‖² — the form yOf's argument is written in — have the same hitting event, so hprop_of_hincl may be read at either.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
