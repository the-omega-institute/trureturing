using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class ThermalOperationDegeneracyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Resource/vomende2022thermaloperations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite Gibbs bath gives a qutrit thermal operation outside the closure of all operations with bath energy-level degeneracy at most three.",
        H("Bath degeneracy can exceed the system dimension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A qutrit refutes the bath degeneracy cap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The qutrit energies are 0, 1 and 2 and the inverse temperature is log 2. "
                        + "Adjoin an independent Gibbs bath, conjugate by a unitary that commutes with total energy, and trace out the bath. "
                        + "These are the hypotheses of thermal operations in Eq. (1). Section V asks whether bath energy-level degeneracy can be capped at the system dimension. "
                        + "In an energy basis the bath Hamiltonian has an arbitrary finite real spectrum. "
                        + "A change of bath basis conjugates both the Gibbs state and the joint unitary, preserving the eigenspace dimensions and the partial trace.")),
                    Paragraph(Text(
                        "Evaluate every operation on the same diagonal input with populations (0, 2/3, 1/3). "
                        + "In the total-energy shell t, the excited inputs with nonzero weight have a common weight proportional to 2 raised to −t. "
                        + "The number of those inputs and the number of ground outputs both bound the total transfer coefficient into the ground outputs. "
                        + "Each row and each column of the matrix of squared unitary entries sums to one.")),
                    Paragraph(Text(
                        "Write g(t) for the bath multiplicity at energy t and d(t) for its excess over g(t − 1) + g(t − 2), truncated at zero. "
                        + "A four-by-four potential table gives an inequality for each triple of multiplicities between zero and three. "
                        + "The two potential terms cancel in the Gibbs-weighted sum because a unit shift halves the weight. "
                        + "The partition sum is therefore at most 11/4 times the weighted excess. The ground output is bounded by 28/33.")),
                    Paragraph(Text(
                        "The bath with energies 0 through 5 and multiplicities (1, 1, 2, 3, 5, 8) has partition sum 47/16. "
                        + "In each of the shells with energy 1 through 5, exchange its ground basis vectors with the equally many excited basis vectors. The ground vector in shell zero stays fixed. "
                        + "The ground output becomes 124/141, above 28/33 by 16/517. Evaluation of a fixed matrix entry on a fixed input is continuous, so the gap also separates the corresponding channel from limits of cap-three operations."))),
                DescribeRole.Theorem))));
}
