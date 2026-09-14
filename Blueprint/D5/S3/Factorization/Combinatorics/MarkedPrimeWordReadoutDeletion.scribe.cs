using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class MarkedPrimeWordReadoutDeletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked Prime Word Readout and Deletion.",
        H("Marked Prime Word Readout and Deletion"),
        Blocks(
            Paragraph(Text(
                "A marked word consists of a prime word with product n and a set of k minus one "
                + "internal positions. Its readout lists one, the prefix products at the sorted "
                + "positions, and n. These prefix products form a strict divisor chain. "
                + "The marked word retains the complete word; the strict chain records only the "
                + "selected products. Each marked copy carries its word mass divided by the "
                + "binomial number of mark selections, and the readout mass sums these copy "
                + "masses over the corresponding fibre. The deletion kernel assigns one over k "
                + "when one of the k internal vertices is omitted, and zero otherwise.")),
            Describe.Lean(
                DescribeId.Create("markedprimewordreadoutdeletion-actual-readout-deletion"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MarkedPrimeWordReadoutDeletion.actual_readout_deletion"),
                H("Exact deletion of marked prime word readouts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n greater than one and k between one and the total prime multiplicity "
                    + "of n minus one, every row of the internal-vertex deletion kernel sums to one. "
                    + "For any real mass on prime words, the readout mass at level k is obtained "
                    + "by applying this kernel to the readout mass at level k plus one. "
                    + "Each smaller mark selection has exactly the total prime multiplicity "
                    + "minus k extensions, and erasing a selected position removes precisely "
                    + "the corresponding prefix-product vertex. The binomial normalizations "
                    + "therefore give the same mass on each coarse readout. Applying the same "
                    + "identity to word masses multiplied by their Boltzmann factors gives "
                    + "the deletion identity for partition masses, with the kernel factor retained."))),
                DescribeRole.Theorem))));
}
