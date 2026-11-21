using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class BinaryPureRecordDecodingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/BinaryPureRecordDecoding.";
    private static LibraryNoteRef EldarForney =>
        LibraryNoteRef.Create("D5/L/Entropy/eldarforney2001quantumdetection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent fair binary pure records have an attained joint guessing optimum on their original product carrier.",
        H("Joint decoding of binary pure records"),
        Blocks(
            Describe.Lean(DescribeId.Create("product-record-success"),
                DeclarationHandle.Create(Module + "pGuess_coordinateProductRecord"),
                H("Exact full-word guessing probability on the original carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EldarForney),
                Blocks(
                    Paragraph(Text("At each position choose an independent fair bit and encode it using a normalized pair of vectors on that position’s finite carrier. The joint density state is the rank-one state of the product of these amplitudes.")),
                    Paragraph(Text("For each coordinate let s be the modulus of its pair’s overlap. The maximum whole-word success is the product of (1 + sqrt(1 - s^2)) / 2 over all coordinates. Partial isometries identify the occupied subspaces, including one-dimensional spans. The empty word has success one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("product-record-attainment"),
                DeclarationHandle.Create(Module + "isGreatest_pGuess_productRecord"),
                H("A full-carrier joint POVM attains the optimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EldarForney),
                Blocks(Paragraph(Text("For repeated copies of a common normalized pair, the guessing probability is the greatest element of the actual success set. An attaining family of positive semidefinite matrices sums to the identity on the original product carrier. The greatest-element property bounds the success of every joint POVM on that carrier."))),
                DescribeRole.Theorem))));
}
