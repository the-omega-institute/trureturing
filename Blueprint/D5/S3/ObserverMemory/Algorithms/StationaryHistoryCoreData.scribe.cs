using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryCoreDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual core data from original controller targets.",
        H("StationaryHistoryCoreData"),
        Blocks(
            Result("actual_core_data", "actual-core-data", "Unrestricted original structural interface",
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.Instances(StationaryHistorySlotGraphDocument.At("CoreData"), StationaryHistorySlotGraphDocument.Call("Fintype", StationaryHistorySlotGraphDocument.V("Q")))),
                "CoreData collects the proved actual incidence, degree, two-row, production and resolving "
                + "counts, selected-target count and outside-B property, target identities and distinct "
                + "resolving rows, s<=J, pure unary structure, N core and e extra targets, and the original "
                + "ActualRead cardinal N+1+e. It also contains the disjoint exact target partition, strict "
                + "binary representative bound, exact binary/selected-literal baseline assignments, all "
                + "actual tail bounds, core digit occupancy, absence of extra background, and indexed "
                + "history separation. This is the structural input to the subsequent weighted inventory; "
                + "it states no overlap correction, weighted necessary inequality, zero-correction theorem, "
                + "synthesis, or global capacity conclusion."))));

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryHistorySlotGraphDocument.ResultAt("StationaryHistoryCoreData", declaration, id, title, statement, explanation);
}
