using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class PositiveWindowObservationBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit observation floor on every positive window", H("An explicit observation floor on every positive window"), Blocks(
            Describe.Lean(DescribeId.Create("positive-window-observation-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/PositiveWindowObservationBound.positive_window_observation_bound"),
                H("Finite derivative coercivity forces every positive window"), StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let K be the real or complex field, V a nonzero Hilbert space over K, W an inner-product space over K, and B:V→V and C:V→W bounded linear maps. Both spaces may be infinite dimensional; W need not be complete.")),
                    Paragraph(Text("Define a(B,C,T) as the infimum over ‖x‖=1 of the actual integral from 0 to T of ‖C exp(tB)x‖^2. Define mu(B,C,N) as the infimum on the same unit sphere of the sum of ‖C B^k x‖^2 for 0≤k≤N. These are genuine real infima; neither is assumed attained.")),
                    Paragraph(Text("For N≥0, H(N) has entries 1/(i+j+1), 0≤i,j≤N, and lambda(N) is its least eigenvalue. Put b=max(1,‖B‖), c=‖C‖, d(N,mu)=sqrt(lambda(N) mu)/N!, r(B,C,N)=c exp(b) b^(N+1)/((N+1)! sqrt(2N+3)), tau(B,C,N,mu)=min(1,d(N,mu)/(2r(B,C,N))), and alpha(N,mu)=lambda(N) mu/(4(N!)^2).")),
                    Paragraph(Text("Suppose mu>0 and mu≤mu(B,C,N). The derivative inequality forces C to be nonzero, so r is strictly positive and the cutoff is defined with a positive denominator. The displayed conclusions hold for every T>0, including N=0 and equality at the cutoff.")),
                    Paragraph(Text("For a unit state, the degree-N Taylor polynomial has energy at least d^2 T^(2N+1) when T≤1. The remainder has energy at most r^2 T^(2N+3). At T≤tau this is at most one quarter of the polynomial floor.")),
                    Paragraph(Text("For an infinite-dimensional example with a necessary first derivative, take V=ℓ²(N,R)⊕₂ℓ²(N,R), W=ℓ²(N,R), B(u,v)=(v,0), and C(u,v)=u. Here B²=0, the zeroth derivative floor is zero, and the first derivative energy is ‖u‖²+‖v‖², so its unit-sphere floor is at least one. Taking N=1 and mu=1 gives a positive cubic short-window lower bound despite the nontrivial kernel of C.")),
                    Paragraph(Text("The squared norm inequality ‖p‖^2≤2‖f‖^2+2‖f-p‖^2 then gives one quarter of the leading energy for f(t)=C exp(tB)x. Nonnegative integral monotonicity extends the bound from min(T,tau) to T. Taking the unit-sphere infimum proves the uniform estimate without compactness, separability, spectral stability, or an eigenvector of the observation operator."))), DescribeRole.Theorem))));

    private static Formula Bound()
    {
        Formula k = F.Id("K"), v = F.Id("V"), w = F.Id("W"), b = F.Id("B"), c = F.Id("C"),
            n = F.Id("N"), m = Mu, T = F.Id("T");
        Formula r = App(F.Id("r"), b, c, n), tau = App(Tau, b, c, n, m);
        Formula floor = Seq(App(Alpha, n, m), Pow(App(Min, T, tau), Seq(D(2), n, Plus, D(1))));
        return Disp(Seq(Forall, Sp, k, Comma, Sp, v, Comma, Sp, w, Comma, Sp,
            OpenBracket, App(F.Id("RCLike"), k), CloseBracket, Sp,
            OpenBracket, App(F.Id("HilbertSpace"), k, v), CloseBracket, Sp,
            OpenBracket, App(F.Id("Nonzero"), v), CloseBracket, Sp,
            OpenBracket, App(F.Id("InnerProductSpace"), k, w), CloseBracket, Comma, Sp,
            Forall, Sp, b, Colon, Sp, App(F.Id("BoundedLinearMap"), k, v, v), Comma, Sp,
            Forall, Sp, c, Colon, Sp, App(F.Id("BoundedLinearMap"), k, v, w), Comma, Sp,
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, m, Comma, Sp, T, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Lt, Sp, m, Sp, Land, Sp, m, Le, Sp, App(F.Id("mu"), b, c, n), Sp, Land, Sp,
            D(0), Lt, Sp, T, Rightarrow, RowBreak, Grp(),
            D(0), Lt, Sp, r, Sp, Land, Sp, D(0), Lt, Sp, tau, Sp, Land, Sp,
            floor, Le, Sp, App(F.Id("a"), b, c, T), Sp, Land, Sp, D(0), Lt, Sp, floor));
    }

    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
}
