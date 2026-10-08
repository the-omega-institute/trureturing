using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual full histories derive unrestricted slot edges, incidence statistics, and degree balances.",
        H("StationaryHistoryIncidence"),
        Blocks(
            Paragraph(Text(
                "Fix P greater than one, arbitrary finite ell and h, a stationary controller C on Q, "
                + "and Initialized C hP ell h. The original physical period is 3P and its digit alphabet "
                + "has three elements. Every original label begins at the same nominal initial state. "
                + "Waits remain positive literal integers, including modular wraps; singleton continuation "
                + "and every control cycle terminating on all initialized inputs remain in scope. "
                + "Only actual read states enter the slot graph. The full nominal carrier Q, including unused "
                + "states, remains the carrier of C and is not replaced by that graph.")),
            Paragraph(Text(
                "Node is the finite type History C hP I of complete indexed read prefixes from "
                + "StationaryReadHistory. A node n has slot row(n)=(readControl(n),color(n)). "
                + "Rows is the image of all nodes; nonroots retains every node with a parent. "
                + "Edges is the image of nonroot nodes under n maps to (row(parent(n)),row(n)). "
                + "Equal slot pairs define one graph edge, while their fibers retain every distinct "
                + "full history. Incoming and outgoing are the edge fibers at their second and first "
                + "endpoints. J sums incoming degree minus one over actual nonroot rows; Xi sums "
                + "edge-fiber cardinality minus one over actual edges. These are derived quantities.")),
            Result("actual_edge_incidence", "actual-edge-incidence", "Actual forest-edge multiplicity",
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.SumOver("z", StationaryHistorySlotGraphDocument.At("nonrootRows"),
                    Seq(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.SetOf("n", StationaryHistorySlotGraphDocument.At("nonroots"), StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.At("row", StationaryHistorySlotGraphDocument.V("n")), StationaryHistorySlotGraphDocument.V("z")))), Minus, D(1))),
                    Seq(StationaryHistorySlotGraphDocument.At("J"), Plus, StationaryHistorySlotGraphDocument.At("Xi")))),
                "The raw_history_surplus supplier is applied to the actual physicalForest and actual row map. "
                + "The counted fiber consists of different full prefixes, not source visits or repeated drawings."),
            Result("outgoing_degree", "outgoing-degree", "At most two distinct outgoing slots",
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.All("n", StationaryHistorySlotGraphDocument.Hist, StationaryHistorySlotGraphDocument.LE(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("outgoing", StationaryHistorySlotGraphDocument.At("row", StationaryHistorySlotGraphDocument.V("n")))), D(2)))),
                "One actual source row fixes its literal delay and next read target. Exact reuse of the "
                + "digit-translation supplier confines all of its children, across every full history and "
                + "read level, to two absolute target digits. This bound includes pure resolving rows "
                + "containing several unary histories."),
            Paragraph(Text(
                "Binaries is the set of histories with exactly two children. ProductionRows is their "
                + "row image. Binary-row uniqueness makes this image injective. TwoRows consists of "
                + "actual rows having two distinct outgoing graph edges; resolvingRows is TwoRows "
                + "minus ProductionRows. Terminal-row uniqueness gives 3P different terminal rows. "
                + "The three roots have no incoming edge and share the first read control. "
                + "Writing N=3(P-1), the graph degree balance gives the following exact counts.")),
            Result("two_outgoing_count", "two-outgoing-count", "Production and pure resolving counts",
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.And(StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("twoRows")), Seq(StationaryHistorySlotGraphDocument.NBinary, Plus, StationaryHistorySlotGraphDocument.At("J"))),
                    StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("productionRows")), StationaryHistorySlotGraphDocument.NBinary),
                    StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("resolvingRows")), StationaryHistorySlotGraphDocument.At("J")))),
                "The incoming balance is |edges|+3=|rows|+J. The outgoing balance is "
                + "|edges|+3P=|rows|+|TwoRows|. Their difference forces |TwoRows|=N+J; "
                + "subtracting N production rows leaves exactly J pure resolving rows."),
            Paragraph(Text(
                "An actual row representative is a selected full history on that row. Target(z) and "
                + "literal(z) are its next target and literal wait, independent of the representative "
                + "on a continuing row. Targets is the set of actual nonfirst read controls. G is the "
                + "target image of TwoRows. For each q, twoAt(q) is the two-row fiber at q, targetSlots(q) "
                + "is its nonroot digit-slot fiber, and targetJ(q) sums the incoming surpluses of those slots.")),
            Result("target_incidence", "target-incidence", "Distinct two-row incidence at a target",
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.All("q", StationaryHistorySlotGraphDocument.V("Q"), StationaryHistorySlotGraphDocument.And(
                    StationaryHistorySlotGraphDocument.LE(Seq(D(2), Times, StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("twoAt", StationaryHistorySlotGraphDocument.V("q")))), Seq(D(3), Plus, StationaryHistorySlotGraphDocument.At("targetJ", StationaryHistorySlotGraphDocument.V("q")))),
                    StationaryHistorySlotGraphDocument.LE(Seq(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("twoAt", StationaryHistorySlotGraphDocument.V("q"))), Minus, D(1)), StationaryHistorySlotGraphDocument.At("targetJ", StationaryHistorySlotGraphDocument.V("q")))))),
                "t different two-outgoing rows give 2t different incoming edges at their common target. "
                + "At most three digit slots subtract at most three first incidences. Nonnegative "
                + "surplus gives t-1<=targetJ(q), including t=0 and t=1. Summing these bounds "
                + "and the actual J balance proves |G|>=N without degree or collision restrictions."))));

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryHistorySlotGraphDocument.ResultAt("StationaryHistoryIncidence", declaration, id, title, statement, explanation);
}
