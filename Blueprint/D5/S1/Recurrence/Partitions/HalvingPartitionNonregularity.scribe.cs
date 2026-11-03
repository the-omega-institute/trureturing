using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionNonregularityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact halving-partition lists and the unrestricted finite integral family question.",
        H("Halving partitions and finite integer families"),
        Blocks(
            Paragraph(Text("Alekseyev, Halving Partitions and Hyperbinary Expansions, "
                + "arXiv:2611.01243v1, Definition 1 and section 6, asks whether its counting "
                + "sequence belongs to a finite family closed under both binary decimations. "
                + "No answer to that question is asserted here.")),
            Paragraph(Text("SourceLists(n) consists of all finite ordered lists of positive "
                + "natural numbers with sum n. The virtual predecessor is n. Each next value "
                + "is either the lower or upper integer half of the preceding value. This is "
                + "a disjunction of value equalities, so equal half values are counted once. "
                + "Repeated parts and all lengths, including terminal ones, are retained. "
                + "The count is Nat.card of these source lists, independent of any formula. "
                + "The sourceEquiv map preserves the whole list and supplies finiteness "
                + "through Mathlib's existing Composition carrier.")),
            Paragraph(Text("MatrixFamily quantifies over every positive dimension, every "
                + "integer vector sequence on all natural inputs, and two fixed integral "
                + "matrices. Coordinate zero is the source count; the even and odd vectors "
                + "are the respective matrix-vector products. ClosedFamily instead indexes "
                + "the constituent integer sequences and states each row as a fixed integer "
                + "linear combination. Neither definition assumes a basis, independence, "
                + "invertibility, bounded dimension, finite alphabet, or eventual validity.")),
            Paragraph(Text("The unresolved counting obligation is an exhaustive, injective "
                + "classification of lists at total 2^m+1. For m at least two, the candidate "
                + "count is three plus the number of positive r with 2^r+r+1 at most m. "
                + "This equality, its sparse first difference, the matrix-power recurrence "
                + "bridge and the unrestricted contradiction require proofs. The negative "
                + "event is expressed as claim; there is no result theorem.")))));
}
