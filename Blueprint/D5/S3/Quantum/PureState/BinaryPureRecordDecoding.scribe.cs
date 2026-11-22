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
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-coordinate-record-isometry"),
                DeclarationHandle.Create(Module + "exists_coordinateRecord_isometry"),
                H("The strict-overlap Walsh carrier embeds in the original product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("When all overlap moduli are below one, an isometry maps each canonical Walsh conditional density to the corresponding original product density. Rephasing each pair makes the overlap real and preserves the conditional densities."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("active-coordinate-record-isometry"),
                DeclarationHandle.Create(Module + "exists_activeRecord_isometry"),
                H("The active Walsh carrier embeds even at overlap one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Choose the active coordinates by the strict overlap condition. An isometry transports the resulting Walsh density to each original whole-word density using the restriction of that word to its active coordinates. The original full labels remain in the statement."))),
                DescribeRole.Theorem))));
}
