using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualKernelCompactLipschitzDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Lipschitz control for the actual arithmetic kernel", H("Explicit Lipschitz control for the actual arithmetic kernel"),
        Blocks(
            Describe.Lean(DescribeId.Create("actualkernelcompactlipschitz-A"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCompactLipschitz.A"),
                H("Reciprocal arithmetic mass"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A(N) is the finite sum of the actual von Mangoldt values Lambda(n)/n for n<N. The n=0 term is zero under the real division convention."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelcompactlipschitz-P"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCompactLipschitz.P"),
                H("Arithmetic mass"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("P(N) is the finite sum of the actual von Mangoldt values Lambda(n) for n<N."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelcompactlipschitz-L"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCompactLipschitz.L"),
                H("The explicit compact constant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("L(a,b,N) equals one half of exp(b/2)*(A(N)+abs(EulerGamma-1)+b)+P(N)+abs(log(2*pi))+1+abs(log(1-exp(-2*a)))."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualkernelcompactlipschitz-kernel-lipschitz"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCompactLipschitz.kernel_lipschitz"),
                H("Control through arithmetic corners"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every 0<a<=b, every natural N with exp(b)<N, and all real u,v in the closed interval [a,b], abs(K(u)-K(v))<=L(a,b,N)*abs(u-v). The function is the complete actual arithmetic kernel. There is no differentiability premise at any prime-power ramp corner. The finite representation of U is obtained from CompleteMangoldtLaplace.mangoldtPart_eq_range at its original owner. Damping sends max(exp(t)/n-1,0) to max(exp(t/2)/n-exp(-t/2),0). The inner derivative has absolute value at most (exp(b/2)/n+1)/2, and the positive-part map is nonexpansive. Summing with nonnegative Lambda(n) gives (exp(b/2)*A(N)+P(N))/2. The remaining smooth part has derivative one half of exp(t/2)*(EulerGamma-1-t)+log(2*pi)*exp(-t/2)+exp(-t/2)*(trivialT(t)+log(1-exp(-2*t))). The original trivialT derivative and its complete bounds 0<=trivialT<=1 give the remaining terms in L. The convex-interval mean value bound applies to these smooth components; the ramps are never differentiated at their corners."))), DescribeRole.Theorem))));
}
