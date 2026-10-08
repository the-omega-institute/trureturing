using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class ArtificialSourceIncrementContractDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An adaptive quartic perturbation generates a unit pulse source with uniform increments and a controlled Robin tail.",
        H("Artificial source increment and tail contracts"),
        Blocks(Describe.Lean(
            DescribeId.Create("artificial-source-increment-contract"),
            DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceIncrementContract.result"),
            H("The complete source contract"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix a positive real delta. Define eta(s)=s squared times (1-s) squared, epsilon(a)=log(a) exp(-(log a) to the power 1/4), h(delta,a)=a to the power 3/4 times exp((log a) to the power 1/4 divided by two), divided by sqrt(log a), times (log a) to the power delta, and alpha(delta,a)=(1/128)(log a) to the power (2 delta-1) divided by sqrt(a).")),
                Paragraph(Text("A real start A is admissible when every a>=A has log a>=1, epsilon(a)<=1 and 1<=h(delta,a)<=a, and epsilon is antitone on [A,infinity). There exists A0 such that every A>=A0 is admissible. The rest of the conclusions hold for every admissible A, with no further size assumption.")),
                Paragraph(Text("Set a0=A and a(j+1)=a(j)+h(delta,a(j)). The grid is strictly increasing and a(j)>=A+j, so it covers the half-line by locally finite cells. On [a(j),a(j+1)], set f(x)=-alpha(delta,a(j)) eta((x-a(j))/h(delta,a(j))); extend f by zero below A. Define B(x)=x-f-prime(x)/k(x), where k(x)=(log x+1)/(x squared times (log x) squared). Put Psi(x)=floor(B(x)), q(x)=1/(x log x), and Phi(x)=the integral of (Psi(v)-v)k(v) over v>x.")),
                Paragraph(Text("The assembled function f is C1 on [A,infinity). The coordinate B is continuous and strictly increasing there, and is C-infinity on every open cell (a(j),a(j+1)). This is smoothness of every finite order, expressed by ContDiffOn of order infinity; no seam differentiability is asserted. Inside a cell its derivative perturbation is a polynomial divided by the smooth nonzero Robin kernel. Psi is integer valued, nonnegative and monotone. For each x>=A, the right-hand limit of Psi is its value Psi(x). For x>A with B(x)=n an integer, Psi(x)=n and its left-hand limit is n-1, so the event has unit positive mass. If B(x) is not an integer, Psi is locally constant at x. For every real a>=A and every real b, the set of integer crossings in [a,b] is finite.")),
                Paragraph(Text("For every a>=A and every t>=0, the absolute value of Psi(a+t)-Psi(a)-t is at most epsilon(a)t+1. The right derivative of B on each cell differs from one by at most epsilon(x) and also by at most one half. A right-derivative mean-value estimate applies across the seams. Antitonicity of epsilon gives the interval budget; the two rounding errors cost at most one.")),
                Paragraph(Text("For every x>=A, the absolute value of Psi(x)-x is at most (1/32)x to the power 3/4 times (log x) to the power (delta+1/2), plus one. For every fixed c0>0, Psi(x)-x is O(x exp(-c0 sqrt(log x))) as x tends to positive infinity. Each fixed logarithmic power is eventually bounded by x to the power 1/8, while exp(c0 sqrt(log x)) is eventually bounded by x to the power 1/8.")),
                Paragraph(Text("For every x>=A the actual integrand (Psi(v)-v)k(v) is absolutely integrable over v>x, and f(x)-q(x)<=Phi(x)<=f(x). The derivative of f is integrable because its magnitude is O(v to the power -9/8). Its integral on the tail is -f(x): integrability gives a limit for f, and the zero values along the unbounded grid force that limit to be zero. The remaining rounding term is between -k and zero, and the integral of k is q(x)."))),
            DescribeRole.Theorem))));
}
