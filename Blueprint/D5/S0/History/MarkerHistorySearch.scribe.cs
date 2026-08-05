using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class MarkerHistorySearchDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/History/MarkerHistorySearch",
            "Marker histories admit exhaustive finite length layers and verified bounded counterexample search."),
        H("Marker History Search"),
        Blocks(
            Paragraph(
                Text("The two-constructor marker alphabet gives a finite list of every history at each exact length. The theorem `mem_historiesOfLength_length` proves that each history occurs in its own layer; concatenating layers through a natural-number bound therefore covers every history whose length is at most that bound.")),
            Paragraph(
                Text("A finite reading is an executable function from marker histories to `Bool`, with `false` designated as rejection. The bounded search inspects the finite layers in increasing length order. `findCounterexample_sound` proves that every returned history is rejected, while `findCounterexample_complete` proves that any rejected history within the supplied bound forces some returned counterexample.")),
            Paragraph(
                Ref("D5/S0/History/MarkerHistorySearch"),
                Text(" includes an executable non-vacuity witness: for the reading that accepts empty histories and histories beginning with `E0`, bound one returns the one-marker history `[E1]`. The bound is explicit, so this construction makes no false claim that an unbounded search terminates when no counterexample exists."))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/HistoryCarrier"))]));
}
