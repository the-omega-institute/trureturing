using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class WeightedSlaterPairCutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary marginal rank for disjoint orbitals with two nonzero endpoint amplitudes.",
        H("Binary alternation rank for the weighted Slater marginal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-ordered-marginal-rank"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fermionic/WeightedSlaterPairCut.orderedMarginal_rank_of_nonzero"),
                H("Rank with both endpoints available"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Split a finite linearly ordered site set into the retained side and " +
                        "its complement. Choose disjoint two-site pairs on each side, with the " +
                        "false endpoint earlier than the true endpoint. Assign an arbitrary " +
                        "nonzero complex amplitude to every endpoint. Form the ordered Slater " +
                        "cut matrix B using these columns in retained-first column order. " +
                        "No normalization of the amplitudes is required.")),
                    Paragraph(Text(
                        "Let A be the binary matrix whose entries indicate whether the two " +
                        "pairs alternate in site order. The matrix B times its conjugate " +
                        "transpose has rank two to the power of the rank of A over the field " +
                        "with two elements. The row carrier includes all occupations. " +
                        "Empty pair lists and rank zero are included.")),
                    Paragraph(Text(
                        "On occupations that choose one endpoint from each pair, the actual " +
                        "determinants give separate amplitude products and the binary " +
                        "character of the cross interaction. The character descends to the " +
                        "two images of the alternation matrix and its transpose. Normalize " +
                        "the separate amplitude vectors on each nonempty fiber to obtain " +
                        "the left and right isometries. Orthogonality of the image characters " +
                        "gives full rank on the image, and the positive fiber masses supply " +
                        "invertible row and column scalings. The supporting occupations " +
                        "embed isometrically into the full carrier."))),
                DescribeRole.Theorem))));
}
