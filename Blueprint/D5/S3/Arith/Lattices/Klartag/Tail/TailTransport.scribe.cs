using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailTransport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail Transport"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail transport to the stochastic ellipsoid construction.")),
            Node("claim-1", "measure_hitSet_fst", "measure hit Set fst",
                "The transport. hitSet M N does not read the padding coordinates, so its probability under the padded measure is its probability under the chain's measure.", DescribeRole.Theorem),
            Node("claim-2", "hit_tail_yOf", "hit tail y Of",
                "Proposition 4.1 at horizon t, about the chain's measure alone. Klartag's M₀ is the initial gap a₀ − (α·r)⁻² and q = 1, so the tail's argument is yOf a₀ t (α·r) — the profile's own argument, by TailAtStep.tail_arg_eq.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
