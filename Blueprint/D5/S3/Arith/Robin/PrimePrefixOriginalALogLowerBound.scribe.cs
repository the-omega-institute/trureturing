using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimePrefixOriginalALogLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original A has a complete positive logarithmic tangent gap and strict two-sided bounds.",
        H("The Original A as a Curvature-Weighted Logarithmic Gap"),
        Blocks(
            Paragraph(Text(
                "Use the same literal actualPhi, its actual second derivative B(v), "
                + "the original complete two-piece constant A, and k=exp(Euler's "
                + "constant)-1. On the full positive axis define "
                + "g(v)=(k*v-1-log(k*v))*B(v).")),
            Describe.Lean(
                DescribeId.Create("prime-prefix-original-a-log-lower-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PrimePrefixOriginalALogLowerBound.result"),
                H("The exact positive gap and strict logarithmic lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The complete g kernel is absolutely integrable on (0,infinity). "
                        + "Its full integral equals A-k*log(k) and is strictly positive. "
                        + "Consequently the same original constant satisfies "
                        + "k*log(k)<A<1/2.")),
                    Paragraph(Text(
                        "PrimePrefixCurvatureMoments supplies the existing complete "
                        + "curvature mass k, first moment 1, logarithmic integrability "
                        + "and literal binding A=-integral log(v)*B(v). The pointwise "
                        + "log product identity makes g a linear combination of those "
                        + "three integrable kernels. Their full moment identities pay "
                        + "the exact cancellation leaving A-k*log(k).")),
                    Paragraph(Text(
                        "Mathlib's logarithmic tangent makes g nonnegative everywhere "
                        + "on the positive axis and strictly positive for v>2/k. "
                        + "PrimePrefixPhiCurvature supplies B(v)>0 at every positive "
                        + "v. The strict positive-integral support criterion therefore "
                        + "pays strictness using a positive-measure tail subset. "
                        + "Every integral retains its full original domain.")),
                    Paragraph(Text(
                        "The original A and excess k are reused literally from "
                        + "PrimePrefixOriginalShoulder. The original upper bound is "
                        + "consumed from PrimePrefixOriginalA. The complete moment "
                        + "and curvature provenance remains with their existing owners; "
                        + "Mathlib supplies the classical logarithmic tangent and "
                        + "positive-integral criterion. This is the explicit full-gap "
                        + "realization of actual-prefix theory section 450. The full "
                        + "Robin pairing and remaining signed tail are separate obligations."))),
                DescribeRole.Theorem))));
}
