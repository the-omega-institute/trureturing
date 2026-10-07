using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped8R5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8R5.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped8R5"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped8r5 to the stochastic ellipsoid construction.")),
            Node("claim-1", "BandHypR2", "Band Hyp R2",
                "DriftStopped8R.BandHypR at the generic reach window.", DescribeRole.Definition),
            Node("claim-2", "windowR2_sub", "window R2 sub",
                "The outer radius of the generic reach window.", DescribeRole.Theorem),
            Node("claim-3", "bandHypR2_of_pos", "band Hyp R2 of pos",
                "The band at windowR2, for every admissible c₃. mAt n c₃ ≥ mR2 n (85a's mAt_ge_mR2) and reachNum2 n = 1/√(mR2 n), so a lattice point beyond the window is beyond the reach of *any* state with lower bound mAt n c₃.", DescribeRole.Theorem),
            Node("claim-5", "bandSideAdoptedR2", "band Side Adopted R2",
                "BandSideAdoptedR2 is a theorem for every admissible threshold family.", DescribeRole.Theorem),
            Node("claim-6", "windowOfR2", "window Of R2",
                "W_g at the generic reach window, over 85b's RawDataInst2RW2.shellR.", DescribeRole.Definition),
            Node("claim-9", "filter_eq_windowOfR2", "filter eq window Of R2",
                "Rule 16: any other open Classical filter of the same predicate is this Finset.", DescribeRole.Theorem),
            Node("claim-10", "avoid_of_casesR2", "avoid of cases R2",
                "DriftStopped8.avoid_of_cases at windowR2.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
