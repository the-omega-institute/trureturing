using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailAtStepRW2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepRW2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail At Step RW2"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail at step rw2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "tail_at_stepRW2", "tail at step RW2",
                "Proposition 4.1 at step k, in the profile's language. From the Φ form of the padded tail at horizon k·h to the profileAt form ContactIntegrated.integrated_count_le consumes.", DescribeRole.Theorem),
            Node("claim-2", "profStepRW2", "prof Step RW2",
                "The per-step profile: Proposition 4.1's value at step time k·h, zero at k = 0.", DescribeRole.Definition),
            Node("claim-4", "tail_of_stepsRW2", "tail of steps RW2",
                "ChainRaw2RW2.tail, discharged. The per-step tail of §1, summed by §2 and §3, at the adopted e = 7 discretisation.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
