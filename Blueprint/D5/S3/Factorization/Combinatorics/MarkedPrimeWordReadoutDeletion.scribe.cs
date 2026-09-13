using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class MarkedPrimeWordReadoutDeletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked Prime Word Readout and Deletion.",
        H("Marked Prime Word Readout and Deletion"),
        Blocks(Paragraph(Text(
            "A marked word consists of a prime word with product n and a set of k minus one "
            + "internal positions. Its readout lists one, the prefix products at the sorted "
            + "positions, and n. These prefix products form a strict divisor chain. "
            + "The marked word retains the complete word; the strict chain records only the "
            + "selected products. Each marked copy carries its word mass divided by the "
            + "binomial number of mark selections, and the readout mass sums these copy "
            + "masses over the corresponding fibre. Boltzmann weighting multiplies the "
            + "word mass by the exponential of negative inverse temperature times word cost. "
            + "The deletion kernel on strict chains assigns one over k when one of the k "
            + "internal vertices is omitted, and zero otherwise.")))));
}
