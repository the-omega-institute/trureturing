using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class StateInvariant4Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/StateInvariant4.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("State Invariant4"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate state invariant4 to the stochastic ellipsoid construction.")),
            Node("claim-3", "measurable_reflStep", "measurable refl Step",
                "The reflected increment is measurable.", DescribeRole.Theorem),
            Node("claim-4", "reflSumPast", "refl Sum Past",
                "The partial sum of reflected increments, read as a function of the past sequence.", DescribeRole.Definition),
            Node("claim-7", "map_reflStep", "map refl Step",
                "The per-step law of the reflected increment: the frozen rotation preserves N(0, c²·Id).", DescribeRole.Theorem),
            Node("claim-8", "indepFun_sum_reflStep", "indep Fun sum refl Step",
                "…and it stays independent of the partial sum before it. The partial sum is reflSumPast ∘ past, a measurable function of the past, so IndepFun.comp applies.", DescribeRole.Theorem),
            Node("claim-11", "countGood", "count Good",
                "The count event. Route M's lift bound is |C_k| · η; this is the event that buys |C_N|, and Chain.chain_snd_mono makes the terminal count dominate every earlier one.", DescribeRole.Definition),
            Node("claim-12", "card_le_of_countGood", "card le of count Good",
                "The contact set only grows, so one bound at N bounds every k ≤ N.", DescribeRole.Theorem),
            Node("claim-16", "measureReal_compl_countGood_le", "measure Real compl count Good le",
                "Markov. The count event fails with probability at most (∫ |C_N|)/c₃.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
