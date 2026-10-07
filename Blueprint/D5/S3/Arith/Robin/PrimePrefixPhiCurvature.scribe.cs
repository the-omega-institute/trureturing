using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimePrefixPhiCurvatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal prime-prefix Phi has positive and strictly decreasing curvature on the nonnegative real axis.",
        H("The Curvature of the Literal Prime-Prefix Phi"),
        Blocks(
            Paragraph(Text(
                "Use the original public actualPhi(v)=exp(integral from 0 to 1 of "
                + "(1-exp(-v*b))/b db) and rate(v)=integral from 0 to 1 of exp(-v*b) db. "
                + "The derivative and zero value belong to the same literal integral model.")),
            Describe.Lean(
                DescribeId.Create("prime-prefix-phi-curvature"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PrimePrefixPhiCurvature.result"),
                H("Positive and strictly decreasing curvature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The actual second derivative has value 1/2 at zero and is strictly "
                        + "decreasing on the entire interval [0,infinity). For every v>0, "
                        + "0<actualPhi''(v)<1/2.")),
                    Paragraph(Text(
                        "The original dominated parameter-integral differentiation gives "
                        + "rate'(v)=-integral from 0 to 1 of b*exp(-v*b) db, including the zero "
                        + "endpoint. Thus actualPhi'' is the concrete model "
                        + "B=actualPhi*(rate^2-rateMoment), and the literal zero value is 1/2.")),
                    Paragraph(Text(
                        "On v>0 the exact curvature is actualPhi(v)*exp(-v)*"
                        + "(v-1+exp(-v))/v^2. Its derivative has the sign of "
                        + "D(v)=1+v-v^2-3*v*exp(-v)-exp(-v)^2. The exponential polynomial "
                        + "T(v)=-exp(2*v)*D(v) has T(0)=T'(0)=T''(0)=0, T'''(0)=1, "
                        + "and T''''(v)=(16*v^2+48*v)*exp(2*v)+3*(v+4)*exp(v)>0 on v>=0. "
                        + "Successive strict monotonicity proves T(v)>0, hence D(v)<0 on the "
                        + "whole positive axis. Continuity of the original integral model extends "
                        + "strict decrease to the zero endpoint.")),
                    Paragraph(Text(
                        "The rate differentiation proof retains its attribution to "
                        + "PrimorialFirstOrderConcentrationCounterexample, and the literal Phi, "
                        + "rate, and finite rate computation retain their attribution to "
                        + "PrimorialGlobalLaplaceEnvelope. The D/T sign chain is the repository's "
                        + "actual-prefix theory section 444.1. The Euler/Ein/E1 normalization "
                        + "and the complete two-piece integral proof of the original A<1/2 "
                        + "remain to be proved separately."))),
                DescribeRole.Theorem))));
}
