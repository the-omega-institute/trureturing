using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class JointDiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete native residue on a common creation diagonal.",
        H("Joint Native Creation Diagonal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-joint-native-diagonal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal.chargedPhysicalResidueRow_joint_native"),
                H("The two ordered chambers have one signed creation total"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(
                    Paragraph(Text("For every original lattice, unimodularity witness, two charges, projected signs, "
                        + "signed lifts and residue indices, and actual pure tensor p tensor g, both matching sector "
                        + "equations give the complete physical residue as one finite pairTranslation sum. The "
                        + "creation total for a supported exponent d is U=-2*(r+n)-gamma-delta-4+Q(sigma)+Q(tau)+d(0)+d(1). "
                        + "For U<0 the whole diagonal is zero. Otherwise m ranges from zero through U.")),
                    Paragraph(Text("Write q=r+l and a=-2*q-gamma-2+Q(sigma)+d(0). The forward contraction contributes "
                        + "H(m-a-2*j), while the reversed contraction contributes H(2*q-(m-a)-2*j). Here H is the "
                        + "actual halfContraction coefficient extended by zero at negative indices. nativeChamberScalar "
                        + "combines the two sums with physicalResidueWeight(q,j) and the exact factor "
                        + "(-1)^q*paritySign(bilinear(sigma,tau)). The two outer ranges remain the actual, separate "
                        + "inner-field order bounds. Neither ordered contribution is asserted to vanish.")),
                    Paragraph(Text("For each forward supported monomial, the contraction cutoff uses its own "
                        + "right coordinate bound; the reverse uses the first coordinate transported by swapping the "
                        + "two variables of pairTranslation. The finite bijections discard only terms with a negative "
                        + "creation index, and preserve arbitrary inhomogeneous oscillator inputs and every signed lift. "
                        + "The tensor factor is the actual ordered ground-action product and the original product of "
                        + "chargeScalar values. The scalar two-chamber change of variables to the four transformed "
                        + "collision kernels remains a separate obligation; this diagonal identity does not supply "
                        + "the forward binomial law, its actual inverse, source-to-Q equality or SectorGroundPair."))),
                DescribeRole.Theorem))));
}
