using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class ChirpedBasisEndpointDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/HilbertOperators/girard2022mixedunitaryrank");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric Werner–Holevo channel in dimension 73 has mixed-unitary rank 2701.",
        H("Symmetric Werner–Holevo rank in dimension 73"),
        Blocks(
            Describe.Lean(DescribeId.Create("has-basis-of-zero"),
                DeclarationHandle.Create(Module + ".hasBasis_of_zero"),
                H("A zero gives a full symmetric unitary basis in order 73"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The 36 multiplicative shifts of the chirped seed and one fixed unchirped seed give 37 seed vectors. The "
                    + "finite pair-coverage check and the involution at the midpoint give orthogonality from the "
                    + "recorded equations. Each seed has 73 modulations, giving 2701 orthogonal symmetric unitaries in "
                    + "a symmetric matrix space of dimension 2701."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mixed-unitary-rank-seventy-three"),
                DeclarationHandle.Create(Module + ".mixedUnitaryRank_seventy_three"),
                H("The minimum mixed-unitary decomposition length is 2701"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The certified zero supplies the basis. Girard et al., Theorem 19(1), identifies the rank "
                    + "criterion. The channel sends X to (tr(X)I + Xᵀ)/74. The basis gives an equal-weight mixture, "
                    + "and the Choi rank gives the matching lower bound for every finite decomposition into unitary "
                    + "conjugations. The construction uses Ma’s Theorem 5 and Proposition 12. The conjecture for every positive "
                    + "dimension remains open."))),
                DescribeRole.Theorem))));
}
