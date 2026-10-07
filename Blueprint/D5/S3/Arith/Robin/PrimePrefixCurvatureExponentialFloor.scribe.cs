using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimePrefixCurvatureExponentialFloorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal curvature has a strict complete exponential floor and a positive exact remainder.",
        H("A Whole-Axis Exponential Floor for the Literal Curvature"),
        Blocks(
            Paragraph(Text(
                "Keep the original actualPhi(v)=exp(integral from 0 to 1 of "
                + "(1-exp(-v*b))/b db) and its actual second derivative B(v). "
                + "The exact remainder is R(v)=B(v)-exp(-v)/2.")),
            Describe.Lean(
                DescribeId.Create("prime-prefix-curvature-exponential-floor"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PrimePrefixCurvatureExponentialFloor.result"),
                H("Strict monotonicity, a complete floor, and the zero endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The function exp(v)*B(v) is strictly increasing on the entire "
                        + "nonnegative axis. For every real v>0, exp(-v)/2<B(v) "
                        + "and the same exact remainder R(v) is strictly positive. "
                        + "At the zero endpoint R(0)=0.")),
                    Paragraph(Text(
                        "The literal closed curvature expression is "
                        + "B(v)=actualPhi(v)*exp(-v)*(v-1+exp(-v))/v^2 for v>0. "
                        + "Differentiating exp(v)*B(v) gives "
                        + "actualPhi(v)*(1-2*v*exp(-v)-exp(-v)^2)/v^3. "
                        + "Its numerator has the sign of exp(v)-exp(-v)-2*v.")),
                    Paragraph(Text(
                        "The last exponential difference vanishes at zero and its "
                        + "derivative exp(v)+exp(-v)-2=(exp(v)-1)^2/exp(v) "
                        + "is strictly positive for v>0. The literal curvature's "
                        + "continuity and value B(0)=1/2 pay the zero endpoint "
                        + "without evaluating a singular positive-axis formula at zero.")),
                    Paragraph(Text(
                        "PrimorialGlobalLaplaceEnvelope supplies the original Phi "
                        + "and first derivative. The consumed all-real rate derivative, "
                        + "second-derivative binding and closed curvature proof retain "
                        + "PrimePrefixPhiCurvature provenance and its original "
                        + "PrimorialFirstOrderConcentrationCounterexample supplier. "
                        + "The exponential sign chain and complete floor are the new "
                        + "content. The remaining Robin signed transport is still open."))),
                DescribeRole.Theorem))));
}
