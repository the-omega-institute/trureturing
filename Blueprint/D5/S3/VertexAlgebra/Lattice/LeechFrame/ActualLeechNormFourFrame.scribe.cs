// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.LeechFrame;

internal sealed class ActualLeechNormFourFrameDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twenty-four explicit orthogonal norm-four charges in the actual Leech lattice.",
        H("The actual Leech norm-four frame"),
        Blocks(
            Paragraph(Text("The index is Fin 12 times Bool. The first entry selects the consecutive coordinates "
                + "2i and 2i + 1, and the second selects the sign on the latter. Each vector has entries "
                + "4 and plus or minus 4 on those coordinates and zero elsewhere. The two directions in "
                + "a pair have dot product zero. Distinct pairs have disjoint supports. The squared "
                + "coordinate length is 32, and the lattice form divides the dot product by eight.")),
            Paragraph(Text("The construction uses IntegerLeech.Admissible for GolayEncoder.code and "
                + "RealLeech.mem_lattice for its unscaled real image. ActualLeechHyperbolic.leechData "
                + "and leechCoordinates are taken from the same witness of "
                + "RealLeech.exists_positive_even_unimodular_gram. The proof uses the rank 24 and "
                + "pairing identity from leech_spec. It has no frame, code, or lattice hypotheses.")),
            Describe.Lean(DescribeId.Create("actual-leech-frame-integral-vector"),
                DeclarationHandle.Create(Prefix + "integralVector"), H("Integral Golay coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use two integer spikes on the chosen coordinate pair."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-leech-frame-admissible"),
                DeclarationHandle.Create(Prefix + "admissible"), H("Golay admissibility"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The common parity is zero, the half-coordinate residue word is "
                    + "the zero word in the Golay code, and the coordinate sum is zero or eight."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-leech-frame-charge"),
                DeclarationHandle.Create(Prefix + "charge"), H("Actual Leech charges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pull back the real image of the admissible vector along "
                    + "the integral equivalence leechCoordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-leech-frame-coordinates"),
                DeclarationHandle.Create(Prefix + "coordinates_charge"), H("Coordinates of each charge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The image in the real Golay coordinate space is the unscaled cast "
                    + "of the chosen integral vector."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-leech-frame-charge-pairing"),
                DeclarationHandle.Create(Prefix + "charge_pairing"), H("Integral Gram pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer bilinear pairing is four on equal indices and zero "
                    + "on unequal indices. The two cases are exposed as charge_norm and charge_orthogonal."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-leech-frame-complex-pairing"),
                DeclarationHandle.Create(Prefix + "complex_pairing"), H("Complex Gram pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the images of the charges in the complex current space, "
                    + "the complex bilinear form g has Gram matrix four times the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-leech-frame-complex-basis"),
                DeclarationHandle.Create(Prefix + "complexBasis"), H("Basis of the complex current space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Orthogonality with nonzero self-pairings gives linear independence. "
                    + "The number of indices equals the dimension of the current space. The basis "
                    + "vector at each index is the complex image of the specified charge."))),
                DescribeRole.Definition))));
}
