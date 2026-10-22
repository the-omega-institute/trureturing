using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockNativeJointSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockNativeJointSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact state-dependent finite support for the full native correction expansion on every original actual tensor.",
        H("Native Correction Joint Finite Support"), Blocks(
            Paragraph(Text("The support is dependent over the original correction shift, the full oscillator "
                + "monomial, and the signed mode tuple for that monomial. It retains the original "
                + "exponent+2*shift, the complete normalSplitCoefficient, every repeated occurrence, and "
                + "the arbitrary ActualTensor target. No global mode cutoff, positivity assumption, "
                + "distinguished-variable inversion, or replacement operator is introduced.")),
            Describe.Lean(DescribeId.Create("actual-native-correction-joint-finite-action"),
                DeclarationHandle.Create(Prefix + "actual_native_correction_joint_finite_action"),
                H("Actual Native Correction Joint Finite Action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original lattice datum, determinant witness, charge, correction "
                        + "polynomial, integer exponent, oscillator polynomial, and arbitrary actual tensor, "
                        + "the native correction coefficient is a finite sum over one dependent index "
                        + "carrying all three coordinates: shift, oscillator monomial, and signed split "
                        + "modes. Outside that single finite set the exact native term is zero, and the "
                        + "coefficient is exactly the finite sum of those terms.")),
                    Paragraph(Text("The proof obtains state-dependent finite mode support for each already-"
                        + "supported shift and monomial, then packages the supports with Finset.sigma. "
                        + "The dependent regrouping is performed by Finset.sum_sigma'; no exchange of "
                        + "unsupported signed-mode and cut sums is used. This is the required joint support "
                        + "statement beyond the earlier aggregated finite-action theorem.")),
                    Paragraph(Text("This theorem identifies only the valid finite regrouping of the native "
                        + "correction expansion. Matching its terms with the full original Lambda/commonKernel "
                        + "diagonal, including creation and annihilation factors, the checked scalar and "
                        + "ground normalizations, the single cocycle, the genuine recurrence and initials, "
                        + "and both unchanged all-j identities remains open. The larger VOA/CFT, "
                        + "anomaly/fusion, string, and AdS/CFT objectives remain open."))),
                DescribeRole.Theorem))));
}
