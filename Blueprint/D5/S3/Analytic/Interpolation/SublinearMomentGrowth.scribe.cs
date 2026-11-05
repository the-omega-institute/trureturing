using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class SublinearMomentGrowthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Interpolation/SublinearMomentGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subexponential growth from finite atomic positivity at sublinear moment order.",
        H("Sublinear moment growth"), Blocks(
            Describe.Lean(DescribeId.Create("sublinear-moment-positive"),
                DeclarationHandle.Create(Owner + "momentPositive"),
                H("Eventual moment-constrained atomic positivity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F:R to R and m:R to N, momentPositive(F,m) means that for every sufficiently large real D, every natural n, every x:Fin n to R with 0<=x(i)<=D, and every a:Fin n to C annihilating sum_i a(i)x(i)^r for every natural r<m(D), the real part of sum_(i,j) a(i)conj(a(j))F(x(i)-x(j)) is nonnegative. Families may be empty, repeated or overlapping; the order function need not be monotone."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sublinear-moment-growth"),
                DeclarationHandle.Create(Owner + "sublinear_moment_growth"),
                H("All-real subexponential growth"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let F:R to R be continuous and even. Let m:R to N be arbitrary, with m(D)>=1 eventually and m(D)/D tending to zero as real D tends to positive infinity. If momentPositive(F,m) holds, then for every real epsilon>0 there exists a real C>0 such that |F(t)|<=C exp(epsilon |t|) for every real t. There is no initial exponential majorant, monotonicity of m, fixed moment order, distinct-node premise, arithmetic hypothesis or RH premise.")),
                    Paragraph(Text("For 1<=p<=n, finite summation by parts proves the exact truncated Newton identity F(n+r)=sum_(q<p) choose(n,q) Delta^q F(r)+sum_(0<=j<=n-p) choose(n-1-j,p-1) Delta^p F(r+j). The nonnegative remainder coefficients sum to choose(n,p). This applies to arbitrary real functions and finite n,p, including p=n.")),
                    Paragraph(Text("Use the binomial weights w(j)=(-1)^j choose(k,j) and the single and double forward-difference identities from PositiveDefiniteImaginaryAxis. Every translated k-stencil annihilates powers of degree below k. Set G(u)=sum_(i,j) w(i)w(j)F(u+i-j). Positivity applied to the sum and difference of the two stencils gives 2G(0)+2G(u)>=0 and 2G(0)-2G(u)>=0, hence |G(u)|<=G(0). This includes a zero diagonal and uses no division. Bijection of the disjoint union of the index blocks to Fin(card) preserves repeated and overlapping nodes.")),
                    Paragraph(Text("The compact envelope M(R)=max(1,sup_(0<=x<=R)|F(x)|) is finite at nonnegative radii by continuity, positive and monotone. Evenness and the stencil l1 norm 2^k give |G(0)|<=2^(2k)M(k), hence |Delta^(2k)F(v)|<=2^(2k)M(k) for v>=0 and v+2k<=D. Set k=m(D), p=2k and D=n+r, 0<=r<=1, in Newton's identity. Bound the low differences on [0,2k+1] and the remainder by the Gram estimate on the same window. This yields |F(n+r)|<=M(2k+1) sum_(q<=2k) 2^q choose(n,q).")),
                    Paragraph(Text("For every sufficiently large real t, n=floor(t), r=t-floor(t) and m(t)/t<1/8 give 2m(t)<=n and 2m(t)+1<=t/2. For 0<z<=1 the truncated binomial sum is at most exp(p/z+2nz): multiply it by z^p, compare termwise with (1+2z)^n and use elementary exponential bounds. Given eta>0, fix z=min(1,eta/6). The original sublinear limit gives 2m(t)<=z^2 t eventually, making the exponent at most eta t at every sufficiently large real t. Therefore |F(t)|<=M(t/2)exp(eta t).")),
                    Paragraph(Text("Choose T>0 beyond this threshold. For R>=2T, split [0,R] at T, absorb the small part in M(R/2), and take the compact supremum to obtain M(R)<=M(R/2)exp(eta R). Finite dyadic induction on R<=2T*2^N proves M(R)<=M(2T)exp(2eta R). Powers of two are unbounded, so every finite nonnegative R is covered without an infinite supremum or an initial growth hypothesis. With eta=epsilon/2, C=M(2T) and R=|t|, evenness gives the conclusion.")),
                    Paragraph(Text("The Reg source owner observes the full original real function through the enrolled DependentFamily.realize template. Its law retains the complete theorem telescope, its actual readout is identity, and its rejected readout is exp(2|t|). The zero input F with m=1 satisfies the hypotheses and rejects that output at epsilon=1. Whole-family sensitivity and observational dependence use this full function state and output; the residual is unknown. The arithmetic construction of a suitable m(D)=o(D) remains an independent open obligation. This conditional analytic theorem supplies neither that construction nor RH."))),
                DescribeRole.Theorem))));
}
