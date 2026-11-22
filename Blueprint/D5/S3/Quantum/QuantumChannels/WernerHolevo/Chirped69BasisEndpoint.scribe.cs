using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class Chirped69BasisEndpointDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/HilbertOperators/girard2022mixedunitaryrank");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric Werner–Holevo channel in dimension 69 has mixed-unitary rank 2415.",
        H("Symmetric Werner–Holevo rank in dimension 69"),
        Blocks(
            Describe.Lean(DescribeId.Create("has-basis-of-zero"),
                DeclarationHandle.Create(Module + ".hasBasis_of_zero"),
                H("A zero gives a full symmetric unitary basis in order 69"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The four seed orbits have lengths 22, 11, 1 and 1. The recorded correlations and finite "
                    + "pair-coverage check give orthogonality of all 35 shifted seeds. The imaginary part of the "
                    + "one midpoint self-correlation vanishes by the orbit involution. The 69 modulations of "
                    + "each shifted seed give 2415 orthogonal symmetric unitaries, the dimension of the full "
                    + "complex symmetric matrix space."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mixed-unitary-rank"),
                DeclarationHandle.Create(Module + ".mixedUnitaryRank"),
                H("The minimum mixed-unitary decomposition length is 2415"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The certified zero of the 63 real equations supplies the basis for the channel "
                    + "X ↦ (tr(X)I + Xᵀ)/70. Girard et al., Theorem 19(1), gives the rank criterion. "
                    + "The basis yields an equal-weight decomposition, and the Choi rank gives the matching "
                    + "lower bound for every finite decomposition into unitary conjugations."))),
                DescribeRole.Theorem))));
}
