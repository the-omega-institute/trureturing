using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class FibonacciBathRecordCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/FibonacciBathRecordCapacity.";

    private static readonly LibraryNoteRef Galke =
        LibraryNoteRef.Create("D5/L/QuantumChannels/galke2023renyisufficiency");
    private static readonly LibraryNoteRef ThermalOperations =
        LibraryNoteRef.Create("D5/L/Resource/vomende2022thermaloperations");
    private static readonly LibraryNoteRef Wheeler =
        LibraryNoteRef.Create("D5/L/Observer/wheeler1999informationphysics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The outgoing six-level Fibonacci bath requires four quantum memory dimensions for exact Gibbs-reference distinguishability.",
        H("Quantum memory for the bath's Gibbs-reference relative entropy"),
        Blocks(
            Paragraph(Text(
                "Wheeler's discussion of apparatus-elicited answers motivates the binary observation "
                + "of whether the terminal qutrit lies in its ground state. The Gibbs preparation of the "
                + "bath also defines a separate comparison question about the bath itself. This "
                + "comparison uses Umegaki relative entropy against the input Gibbs state.")),
            Describe.Lean(
                DescribeId.Create("six-level-likelihood-ratios"),
                DeclarationHandle.Create(Prefix + "sixLevel_likelihood_ratios"),
                H("Exact likelihood ratios for the thermal bath"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Galke, ThermalOperations),
                Blocks(Paragraph(Text(
                    "Tracing out the qutrit in the terminal joint distribution gives the outgoing bath "
                    + "law. Dividing its weights by the positive input Gibbs weights yields the distinct "
                    + "ratios 0, 4/3, 5/3 and 7/3. The zero ratio is attained at the lowest bath level."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("six-level-sharp-gibbs-entropy-dimension"),
                DeclarationHandle.Create(Prefix + "sixLevel_sharp_gibbs_entropy_dimension"),
                H("Four dimensions are necessary and sufficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Galke, ThermalOperations, Wheeler),
                Blocks(Paragraph(Text(
                    "The comparison density is the outgoing bath marginal and the reference density is "
                    + "the actual input Gibbs state. A CPTP encoder preserving their relative entropy "
                    + "needs at least four memory dimensions. An encoder into four dimensions attains "
                    + "equality. The Gibbs preparation and terminal bath specify the physical instance. "
                    + "The general dimension proof takes only the two diagonal densities."))),
                DescribeRole.Theorem))));
}
