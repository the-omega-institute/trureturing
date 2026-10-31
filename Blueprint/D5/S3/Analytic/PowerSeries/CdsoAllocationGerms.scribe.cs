using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PowerSeries;

internal sealed class CdsoAllocationGermsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full CDSO allocation functions have removable analytic extensions and the quadratic Taylor cutoff.",
        H("Actual allocation germs"),
        Blocks(Describe.Lean(
            DescribeId.Create("cdso-actual-allocation-germ-cutoff"),
            DeclarationHandle.Create("D5/S3/Analytic/PowerSeries/CdsoAllocationGerms.allocation_germ_iff_taylor"),
            H("Full allocation functions and their genuine coefficients"),
            StatementSource.FromAuthor(Disp(Seq(
                D(2), Sp, Le, Sp, F.Id("a"), Sp, Implies, Sp,
                Call("AnalyticAtZero", F.Id("E_b")), Sp, Land, Sp,
                Call("AnalyticAtZero", F.Id("E_c")), Sp, Land, Sp,
                Call("PositiveGermEq", F.Id("A_b"), F.Id("E_b")), Sp, Land, Sp,
                Call("PositiveGermEq", F.Id("A_c"), F.Id("E_c")), Sp, Land, Sp,
                Open, Call("PositiveGermEq", F.Id("A_b"), F.Id("A_c")), Sp, Iff, Sp,
                Forall, Sp, F.Id("k"), Sp, Le, Sp,
                D(3), Open, D(6), Open, F.Id("a"), Plus, D(1), Plus, F.Id("h"), Close, Plus, D(5), Close,
                Caret, Grp(D(2)), Comma, Sp,
                Call("TaylorCoeff", F.Id("E_b"), F.Id("k")), Sp, Eq, Sp,
                Call("TaylorCoeff", F.Id("E_c"), F.Id("k")), Close))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix natural a at least two and h. An allocation datum has a branch j with 1<=j<=h, a remainder d<a+j-1, a remainder t<h+1-j, and an arbitrary integer vector z on Fin(a+j). Write m=a+j, r=m-1, n=h+1-j and s=a+1+h. Source-admissible vectors satisfy sum z=n-d, sum z-positive<=n and sum z-negative<=d; the theorem also permits all other integer vectors. Every source residue supplies such d and t, so no residue, branch or allocation is excluded.")),
                Paragraph(Text("The definitions are alpha=(a-1)/r, beta=j/(rn), phi=-(n+(r-1)d)/r, sigma=(d-n)/r, gamma=(n-d)/(rn), v-minus=gamma-t/n and v-plus=v-minus+1. Let delta_i=sigma+z_i, delta_0=sigma+min z, and L=n-sum z-positive. The radical R(b,delta,k,u) is sqrt((b+delta*u)^2+k^2*u^2)/(b+delta*u)-1, with the nonnegative real square root, positive near zero.")),
                Paragraph(Text("A_b is exactly source formula (8.4): two divided by u squared times the sum over i of (alpha+phi*u)R(alpha,delta_i,m,u)+u(d-z_i-negative)R(alpha,delta_i,r,u)+u*z_i-positive*R(alpha,delta_i,2,u), plus uL times the difference of R(alpha,delta_0,2,u) and R(alpha,delta_0,r,u), plus (n-t) times ((beta+(v-minus-1)u)R(beta,v-minus,1,u)+uR(beta,v-minus,2,u)), plus t times the corresponding v-plus expression.")),
                Paragraph(Text("Replace every R/u squared by k squared divided by (b+delta*u)(sqrt((b+delta*u)^2+k squared*u squared)+b+delta*u). This defines E_b, the actual removable analytic extension. TaylorCoeff(E,k) is the k-th iterated real derivative at zero divided by k factorial. PositiveGermEq means equality throughout a sufficiently small positive neighborhood of zero. The cutoff includes its endpoint.")),
                Paragraph(Text("Each allocation is a sum of at most 3m+2+2n<=3s+2 affine-weighted radicals. Repeating each tail entry preserves the case n=1. A pair has at most 6s+4 radicals. Clearing the product of their affine denominators gives polynomial coefficients of degree at most K+1 and quadratic radicands with nonzero constant roots; its rational part is the radicand one. The formal cutoff applies to the genuine Taylor series. Analytic uniqueness, including the one-sided identity theorem, returns the asserted actual germ identity.")),
                Paragraph(Text("There is no frequency-separation condition, new threshold in a, noncancellation assumption or independence hypothesis. Identical radicals and signed, zero or absent weights are retained. The result gives no optimizer reconstruction, least period, uniform arithmetic separation or parameter-growth threshold."))),
            DescribeRole.Theorem))));
}
