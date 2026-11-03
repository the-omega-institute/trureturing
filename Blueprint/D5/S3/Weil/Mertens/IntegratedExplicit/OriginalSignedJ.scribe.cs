using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class OriginalSignedJDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independent inclusive original J identity", H("The independent inclusive original J identity"),
        Blocks(
            Paragraph(Text("Absolute-continuity calculus, interval integration, von Mangoldt arithmetic and Euler normalization are imported from the pinned Apache-2.0 Mathlib. Finite indicator-tail summation and its application to this independently defined J are repository derivations; no RH or sign estimate is a premise.")),
            Describe.Lean(DescribeId.Create("original-signedj-finite-abel-ac"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.finite_abel_ac"),
                H("Finite Abel summation for an absolutely continuous function"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary finite index set, real weights w, knots k in [0,D], gamma, D>=0 and absolutely continuous H, finiteB(t)=gamma-t+sum_{k_i<=t} w_i. The exact identity is sum_i w_i*H(k_i)-integral_0^D H-(gamma-D+sum_i w_i)*H(D)=-gamma*H(0)-integral_0^D finiteB(t)*deriv(H)(t). Integrating each inclusive tail indicator supplies the knot contribution. Empty sets, knots at D and D=0 are included."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-signedj-original-j-identity"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.original_J_identity"),
                H("The inclusive prime-power identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cutoff is all natural numbers from 2 through floor(exp(D)), inclusive; b(t)=EulerGamma-t+sum_{n<=exp(t)} vonMangoldt(n)/n. Independently, J(D,f,fprime)=2*integral_0^D b(t)*exp(t/2)*(fprime(t)+f(t)/2). Assuming D>=0, absolute continuity of f and actual a.e. derivatives fprime, the identity is 2*sum_{n in cutoff(D)} vonMangoldt(n)/sqrt(n)*f(log(n))-2*integral_0^D exp(t/2)*f(t)-2*b(D)*exp(D/2)*f(D)=-2*EulerGamma*f(0)-J(D,f,fprime). The weighted lift H(t)=exp(t/2)*f(t) supplies both the integral and endpoint terms."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-signedj-fullr-eq-original-j"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalSignedJ.fullR_eq_original_J"),
                H("The conditional endpoint substitution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The definition fullR(D,Z,f) retains the same prime-power sum and continuum integral, with endpoint term b(D)*Z/2. Substituting f(D)=-exp(-D/2)*Z/4 yields fullR(D,Z,f)=-2*EulerGamma*f(0)-J(D,f,fprime). This supplier explicitly assumes that endpoint equality; OriginalActualSpectralEndpoint proves it for the actual test and consumes this theorem."))),
                DescribeRole.Theorem))));
}
