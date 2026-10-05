using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailAtStepDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail At Step"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail at step to the stochastic ellipsoid construction.")),
            Node("claim-1", "tail_arg_eq", "tail arg eq",
                "Klartag's tail argument is yOf: with M₀ = a₀ − (α·r)⁻² (eq. 61 at the scaled radius) and q = 1, the argument of Φ in padded_tail_of_increments is yOf a₀ t (α·r).", DescribeRole.Theorem),
            Node("claim-2", "measureReal_le_of_le", "measure Real le of le",
                "An ℝ≥0∞ tail bound read as a real one.", DescribeRole.Theorem),
            Node("claim-7", "dom_of_tail2", "dom of tail2",
                "Params.dom against c · profile. dom_of_tail rescaled; c ≥ 0 is all that is used.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
