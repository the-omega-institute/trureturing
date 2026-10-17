using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class ActualPSDMomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint moments of ordered defects under the actual positive semidefinite constraint.",
        H("Zero-jump actual-PSD defect moment"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-actual-psd-zero-jump-moment"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_zero_jump_moment"),
                H("Continuous joint moment bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
"For arbitrary real h on Fin 5 and d on Fin 9, assume h is antitone and nonnegative, d is monotone with every coordinate between zero and one, and H+D is at most four, where H and D are the respective coordinate sums. The literal symmetric matrix has diagonal entries 2(1-d8), 2(1-d6), 2(1-d3), and upper off-diagonal entries -(h0+d7), -(h1+d5), -(h2+d4). Its positive semidefiniteness implies sum h_i^2 + sum d_i^2 - (H-D)/4 is at most 7/2. All indices are zero based. The statement includes singular matrices and arbitrary ordered tail shapes."
                ))), DescribeRole.Theorem),
            Paragraph(Text(
"Write r=d6+d7+d8 and u=d3. The original ordered-block energy theorem supplies sum d_i^2 at most r^2. The actual PSD matrix also supplies the coupled tail budget via a homogeneous quadratic-form evaluation in the full plus/minus congruence. Combining this budget with ordering gives two further square-sum envelopes. Rational polynomial case splits yield sum d_i^2 at most 9/4."
            )),
            Paragraph(Text(
"For h0 at most 1/2, the head chord estimate and H+D at most four give a joint moment at most 13/4. For h0 at least 1/2, replace the tail by zero and add r to h0. This preserves order and the total budget. In the full congruent Z-matrix it increases entries while keeping off-diagonal entries nonpositive, so it preserves actual positive semidefiniteness. The joint moment increases by 2r(h0-1/2)+(r^2-sum d_i^2)+(3r-D)/4."
            )),
            Paragraph(Text(
"For the resulting flat tail, the PSD determinant gives a^2+b^2+e^2+abe at most four for the first three heads. The other two heads are bounded by a chord and their remaining mass budget. Polynomial comparison reduces the first two heads to a scalar interval with one possible kink; the original quadratic interval theorem and rational endpoint factors give the bound 7/2. This is a statement about continuous real defect data; any physical realization or purity theorem requires its own connection to these hypotheses."
            ))
        )));
}
