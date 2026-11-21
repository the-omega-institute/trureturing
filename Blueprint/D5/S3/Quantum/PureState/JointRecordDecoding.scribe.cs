using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class JointRecordDecodingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/JointRecordDecoding.";
    private static LibraryNoteRef EldarForney =>
        LibraryNoteRef.Create("D5/L/Entropy/eldarforney2001quantumdetection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A phase-basis POVM and a diagonal upper bound give the exact uniform guessing probability.",
        H("Joint decoding in a flat orthogonal phase basis"),
        Blocks(
            Describe.Lean(DescribeId.Create("phase-measurement-attains"),
                DeclarationHandle.Create(Module + "isGreatest_phase"),
                H("The normalized phase measurement attains the upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EldarForney),
                Blocks(
                    Paragraph(Text("On a nonempty finite index type of size N, the phase matrix has unit-modulus entries and its column Gram matrix is N times the identity. The profile t is coordinatewise nonnegative and its squared coordinates sum to one.")),
                    Paragraph(Text("The ensemble is uniform and its vectors are the entrywise products of t with the phase rows. The rank-one effects of the normalized rows sum to the identity and attain (sum_i t_i)^2 / N. The diagonal with entries t_i times sum_l t_l dominates each state matrix. Trace pairing gives the same upper bound for every labelled POVM, including when profile entries vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("walsh-joint-success"),
                DeclarationHandle.Create(Module + "pGuess_coordinateRecord"),
                H("Exact whole-word success for the binary Walsh ensemble"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(EldarForney),
                Blocks(
                    Paragraph(Text("For every finite list of overlaps in [0,1], the canonical binary record has joint guessing probability equal to the product of the factors (1 + sqrt(1 - s^2)) / 2. The Walsh signs are the irreducible characters of the finite abelian group of binary words. Eldar and Forney's geometrically uniform result gives the finite minimum-error measurement for this symmetry.")),
                    Paragraph(Text("The Lean proof uses the explicit normalized Walsh POVM and a diagonal bound. Each coordinate can have overlap zero or one. The empty product has value one."))),
                DescribeRole.Theorem))));
}
