using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimePrefixCurvatureVolterraRecursionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Phi curvature satisfies an exact positive Volterra equation, consumed by strictly increasing actual recursive floors and exact iterated residuals.",
        H("The Actual Curvature's Positive Volterra Recursion"),
        Blocks(
            Paragraph(Text(
                "Retain actualPhi(v)=exp(integral from 0 to 1 of "
                + "(1-exp(-v*t))/t dt) and curvature(v)=deriv(deriv actualPhi)(v). "
                + "The coefficient a(v) is the genuine finite integral "
                + "one half times the integral from 0 to 1 of "
                + "(1-t)^2*(exp(-v*(1-t))+exp(-v*(1+t))).")),
            Describe.Lean(
                DescribeId.Create("prime-prefix-curvature-volterra-recursion"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraRecursion.result"),
                H("An exact equation and its strictly improving actual finite layers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coefficient is continuous on the real line, a(0)=1/3, "
                        + "and 0<a(v)<=1/3 for every v>=0. Its positive-axis "
                        + "closed formula is exp(-v)*(exp(v)-exp(-v)-2*v)/v^3. "
                        + "A finite weighted-exponential primitive binds this "
                        + "quotient to the same integral coefficient; the zero "
                        + "value and continuity use the integral itself.")),
                    Paragraph(Text(
                        "Write lift(f,v)=integral t=0..v of (v-t)*f(t), "
                        + "b(v)=exp(-v)*(1/2+integral s=0..v of a(s)*(1+s)), "
                        + "and T(f,v)=exp(-v)*integral s=0..v of a(s)*lift(f,s). "
                        + "For every v>=0 the result gives the original "
                        + "Phi(v)=1+v+lift(curvature,v), the exact "
                        + "curvature(v)=exp(-v)*(1/2+integral s=0..v of a(s)*Phi(s)), "
                        + "and curvature(v)=b(v)+T(curvature,v).")),
                    Paragraph(Text(
                        "Set B0(v)=0 and B(n+1,v)=b(v)+T(Bn,v). "
                        + "The actual remainder Rn(v)=curvature(v)-Bn(v) "
                        + "equals the n-fold iterate T^n(curvature)(v) "
                        + "for every natural n and v>=0. For every finite n "
                        + "and v>0, 0<=Bn(v)<B(n+1,v)<curvature(v). "
                        + "At zero, B(n+1,0)=1/2 and R(n+1,0)=0 "
                        + "for every n>=0; B0(0)=0 and R0(0)=1/2 by definition.")),
                    Paragraph(Text(
                        "The exact equation is consumed in the residual step "
                        + "R(n+1)=T(Rn) on the nonnegative axis. Finite-integral "
                        + "linearity also gives the increment step D(n+1)=T(Dn). "
                        + "Continuity and actual positive interval integrals "
                        + "give strict positivity of both residuals and "
                        + "increments at every positive v. Strict endpoint "
                        + "claims do not include v=0.")),
                    Paragraph(Text(
                        "The original Phi and first derivative retain "
                        + "PrimorialGlobalLaplaceEnvelope provenance. Consumed "
                        + "private rate, actual-curvature and tilted-derivative "
                        + "bodies retain PrimePrefixCurvatureExponentialFloor, "
                        + "PrimePrefixPhiCurvature and the original "
                        + "PrimorialFirstOrderConcentrationCounterexample source. "
                        + "Mathlib supplies actual interval integrals, FTC, "
                        + "continuous parameter integrals and strict positive "
                        + "interval integration. This is the actual-object "
                        + "recursive unit of theory section 463. Complete "
                        + "factorial and logarithmic-moment convergence interfaces "
                        + "are subsequent obligations; the same-source signed "
                        + "arithmetic transport and RH endpoint remain open."))),
                DescribeRole.Theorem))));
}
