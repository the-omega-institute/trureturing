using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalResidualFiniteTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.";

    private static DocumentBlock Def(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("original-residual-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Helper(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("original-residual-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unchanged finite Mobius floor response admits an explicit residual transfer with both moments, weighted floor variation and exact prefix payments.",
        H("Finite Transfer of the Original Mobius Floor Residual"),
        Blocks(
            Paragraph(Text(
                "All sequences are real-valued on the natural numbers. All logarithms are natural. "
                + "Fix natural N>=3 and 0<=q<=N-2, put h=q+1 and L=log N. "
                + "The integer block is N<=m<2N. Empty sums are zero. The arithmetic "
                + "function mu is Mathlib's actual Mobius function at every index, without "
                + "a prime-only restriction or any modification at prime powers. "
                + "M(k) is the existing full inclusive prefix sum of mu(d) for 1<=d<=k.")),
            Paragraph(Text("The source-bound audit for log_bounds remains declared_unresolved under "
                + "IE-C050/source.unsafe_or_external (Nat.add). The missing source-reconstruction "
                + "binding certificate is tracked at https://github.com/the-omega-institute/trureturing/issues/17873. "
                + "This is an unfinished audit, not a failure of the compiled inequality or evidence "
                + "of a judge defect. The other new helper audits and full-positive transfer audit are validated.")),
            Def("mass", "Absolute block mass",
                "For every natural N and real sequence a, A=mass(N,a)=sum(N<=m<2N,abs(a(m)))."),
            Def("firstAbsoluteMoment", "First absolute moment on the original block",
                "For every natural N and real sequence a, B=firstAbsoluteMoment(N,a)="
                + "sum(N<=m<2N,m*abs(a(m))). The actual integer index remains inside the sum."),
            Def("variation", "Variation of the zero extension",
                "For every N and a, V=variation(N,a)=abs(a(N))+sum(N<=m<2N-1,"
                + "abs(a(m+1)-a(m)))+abs(a(2N-1)). For N>=1 this is precisely the "
                + "variation of a on the block extended by zero outside it. Both jumps remain."),
            Def("floorPair", "The actual integer floors",
                "For every natural N,d and sequence a, H(d)=floorPair(N,a,d)="
                + "sum(N<=m<2N,a(m)*floor(m/d)). The formal definition uses natural "
                + "division; for d>=1 it is exactly the floor of the nonnegative real quotient."),
            Def("logPair", "Logarithmic floor pairing",
                "For every natural N,d and sequence a, G(d)=logPair(N,a,d)=log(N/d)*H(d)."),
            Def("logDifference", "The complete consecutive difference",
                "For every natural N,k and a, J(k)=logDifference(N,a,k)=G(k)-G(k+1)."),
            Def("weightedVariation", "Denominator-weighted variation",
                "For every N,h,a, W=weightedVariation(N,h,a)=sum(h<=k<N,k*abs(J(k)))."),
            Def("coefficient", "Unchanged logarithmic Mobius coefficients",
                "For every natural N,d, alpha(d)=coefficient(N,d)=mu(d)*log(N/d)/log N. "
                + "The coefficient at d=1 is retained, and the logarithmic weight at d=N is zero."),
            Def("response", "The original affine and floor response",
                "For every N,m, response(N,m)=1+C*m-sum(1<=d<=N,alpha(d)*floor(m/d)), "
                + "where C=sum(1<=d<=N,alpha(d)/d). Both the constant and the full linear "
                + "coefficient are included in this definition."),
            Def("residual", "Pairing with the original response",
                "For every N,a, E=residual(N,a)=sum(N<=m<2N,a(m)*response(N,m))."),
            Def("replacement", "High-prefix replacement with the literal constant",
                "For every N,q,a,F, Z=replacement(N,q,a,F)="
                + "-sum(q+1<=k<N,(F(k)+2)*J(k))/log N. The +2 pays a literal -2 "
                + "in a supplied spectral prefix and is not absorbed into an endpoint."),
            Def("centered", "The nonzero integer mean",
                "For all natural d,m, centered(d,m)=(m mod d)/d-(d-1)/(2*d). For d>=1 "
                + "the subtracted mean is the exact average on integer residues, including residue zero."),
            Helper("centered_floor", "The original quotient decomposition",
                "For every natural d>0 and m, floor(m/d)=m/d-centered(d,m)-(d-1)/(2*d), "
                + "where the quotient on the left is natural division and the other quotient is real."),
            Helper("variation_nonneg", "Nonnegative complete variation",
                "For every natural N and arbitrary real sequence a, variation(N,a)>=0, "
                + "including both endpoint absolute values and the entire interior difference sum."),
            Helper("centered_pair_variation_bound", "Centered pairing with both jumps",
                "For natural N,d with N>0 and d>0 and every real sequence a, "
                + "abs(sum(N<=m<2N,a(m)*centered(d,m)))<=d*variation(N,a). "
                + "No moment condition is needed. The same periodic primitive and summation-by-parts "
                + "proof supply the two-moment floor bound and the full positive mean remainder."),
            Describe.Lean(DescribeId.Create("original-residual-centered-pair-variation-sharp-bound"),
                DeclarationHandle.Create(Prefix + "centered_pair_variation_sharp_bound"),
                H("Sharp centered pairing with both jumps"), StatementSource.FromAuthor(SharpBVFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every positive natural N,d and arbitrary real sequence a, let "
                        + "S(N,d,a)=sum(N<=m<2*N,a(m)*centered(d,m)). Then abs(S)<=d*V/16, "
                        + "where V=variation(N,a) includes both zero-extension jumps. No sign or "
                        + "moment hypothesis is imposed, including at N=1.")),
                    Paragraph(Text("For the original private primitive P=r*(r-d)/(2*d), r=m mod d, "
                        + "0<=r<=d and (2*r-d)^2>=0 give -d/8<=P<=0. Hence Q=P+d/16 "
                        + "satisfies abs(Q)<=d/16. The unchanged primitive_step supplies the wrap. "
                        + "Q is not the zero-based prefix: Q(0)=d/16. Before taking absolute values, "
                        + "sum(a(m+1)-a(m))=a(2*N-1)-a(N) cancels the shift exactly. "
                        + "Both coarse and sharp bounds use one private finite by-parts assembly, "
                        + "with boundary terms a(2*N-1)*Q(2*N)-a(N)*Q(N). "
                        + "The new range inference is consumed by the sharper full-positive transfer. "
                        + "This finite estimate does not settle signed infinite transport or RH."))), DescribeRole.Theorem),
            Helper("reciprocal_log_step", "Reciprocal logarithmic step",
                "For every natural k>0, 1/(k+1)<=log(k+1)-log(k)."),
            Helper("weighted_floor_prefix_bound", "Partial floor count with its negative endpoint",
                "For natural h,j,m with 0<h<=j<m, "
                + "sum(h<=k<=j,k*(floor(m/k)-floor(m/(k+1))))"
                + "<=m*(1+log(j/h))-j. The terminal floor(m/(j+1)) is at least one. "
                + "Its negative contribution -j is retained for the later joint cancellation."),
            Helper("weighted_floor_bound", "Weighted original floor count",
                "For natural N,h,m with 0<h<N and m<2*N, "
                + "sum(h<=k<N,k*(floor(m/k)-floor(m/(k+1))))<=2*N*(1+log(2*N/h)). "
                + "The proof keeps the exact terminal floor before taking its upper bound."),
            Helper("log_bounds", "Logarithms on the finite divisor range",
                "For natural N,d with 0<d<=N, 0<=log(N/d)<=log(N)."),
            Helper("weighted_log_step", "Weighted logarithmic step",
                "For every natural k>0, k*(log(k+1)-log(k))<=1."),
            Helper("weightedVariation_firstMoment_bound", "Joint first-moment high variation",
                "For natural N,h with 0<h<=N and arbitrary real a on the original block, "
                + "assume only sum(N<=m<2N,m*a(m))=0. No zeroth moment is required. "
                + "Put u=log(N/h) and B=firstAbsoluteMoment(N,a). Then the unchanged "
                + "weightedVariation(N,h,a)<=B*(u+u*u/2). At h=N both sides vanish. "
                + "The first moment rewrites the floor pair as a negative remainder pair. "
                + "For delta(k)=log(k+1)-log(k), triangular finite summation keeps the "
                + "negative endpoint -j*mass(N,a) until it cancels the entire "
                + "mass(N,a)*sum(k*delta(k)) payment in the product difference. "
                + "Finally sum(delta(k)*log(k/h))<=u*u/2 follows by telescoping squares. "
                + "The existing finite transfer consumes this bound and recovers its old "
                + "public allowance from B<=2*N*mass(N,a); no residual sign follows."),
            Helper("prefix_bound", "Absolute actual Mobius prefix",
                "For every natural q, abs(M(q))<=q, with every original Mobius index retained."),
            Helper("sum_indices", "Exact finite integer sum",
                "For every natural q, sum(1<=d<=q,d)=q*(q+1)/2 as a real identity."),
            Helper("prefix_error_bound", "Shared error for an arbitrary finite difference",
                "For natural N,h with h>0, arbitrary real arrays D,F and real e,c with c>=0, "
                + "if abs(F(k)-M(k))<=e*k+c for h<=k<N, then "
                + "abs(sum(h<=k<N,(F(k)-M(k))*D(k)))<=(e+c/h)*sum(h<=k<N,k*abs(D(k))). "
                + "The statement needs no sign condition on D or vanishing moments."),
            Describe.Lean(DescribeId.Create("original-residual-finite-transfer"),
                DeclarationHandle.Create(Prefix + "originalResidual_finite_transfer"),
                H("The finite two-moment transfer"), StatementSource.FromAuthor(TransferFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N,q be natural with N>=3 and q<=N-2. Let a,F be arbitrary "
                        + "real sequences, and let e,c be real with e>=0 and c>=0. Assume "
                        + "sum(N<=m<2N,a(m))=0 and sum(N<=m<2N,m*a(m))=0 exactly. "
                        + "At every integer h<=k<N assume abs(F(k)-M(k))<=e*k+c. "
                        + "There is no condition on F below h. Then abs(E-Z) is at most "
                        + "((e+c/h)/L)*N*A*(1+2*log(N/h)*(1+log(2N/h)))"
                        + "+h*(3*q/2+2)*V.")),
                    Paragraph(Text(
                        "For d>=1 the centered sawtooth is phi(d,m)=(m mod d)/d-(d-1)/(2*d). "
                        + "Its periodic primitive is P(d,m)=r*(r-d)/(2*d), r=m mod d. "
                        + "The difference P(d,m+1)-P(d,m) equals phi(d,m), including a wrap "
                        + "to residue zero. Since abs(P(d,m))<=d/2, every centered prefix "
                        + "starting at any natural integer is bounded by d. Mathlib's "
                        + "finite summation by parts then gives abs(H(d))<=d*V. The same "
                        + "two moments give H(d)=-sum(a(m)*phi(d,m)); the pointwise "
                        + "sawtooth bound also gives abs(H(d))<=A.")),
                    Paragraph(Text(
                        "At d=1 the floor is m and the first moment cancels it. At d=N "
                        + "all block floors are exactly one and the zeroth moment cancels "
                        + "them. Thus H(1)=H(N)=G(1)=G(N)=0. Expanding the original "
                        + "response cancels its constant by the zeroth moment and its "
                        + "linear term by the first moment, giving E=-sum(mu(d)*G(d))/L. "
                        + "ActualOddMobiusFinitePairing.prefix_abel supplies the full exact identity "
                        + "E=-sum(1<=k<N,M(k)*J(k))/L.")),
                    Paragraph(Text(
                        "Actual weighted floor drops satisfy the exact identity "
                        + "sum(h<=k<N,k*(floor(m/k)-floor(m/(k+1))))="
                        + "h*floor(m/h)+sum(h<=k<N-1,floor(m/(k+1)))"
                        + "-(N-1)*floor(m/N). The terminal floor is nonnegative. "
                        + "The inequalities floor(m/j)<=m/j and "
                        + "1/(k+1)<=log(k+1)-log k telescope to an upper bound "
                        + "m*(1+log(N/h)), which is at most 2*N*(1+log(2*N/h)) "
                        + "on the original block. Expanding the product difference "
                        + "J(k) and using k*(log(k+1)-log k)<=1 therefore proves "
                        + "W<=N*A*(1+2*log(N/h)*(1+log(2*N/h))).")),
                    Paragraph(Text(
                        "The exact low prefix is Pq=sum(1<=k<=q,M(k)*J(k))="
                        + "sum(1<=d<=q,mu(d)*G(d))-M(q)*G(h). Its bound is "
                        + "abs(Pq)/L<=(3/2)*q*(q+1)*V. Telescoping the entire "
                        + "high range gives sum(h<=k<N,J(k))=G(h), so the constant "
                        + "payment is exactly 2*G(h)/L and is bounded in absolute "
                        + "value by 2*h*V. The remaining error is "
                        + "sum(h<=k<N,(F(k)-M(k))*J(k))/L, bounded by "
                        + "((e+c/h)/L)*W using c>=0. Their sum gives the displayed bound.")),
                    Paragraph(Text(
                        "The case q=0 has empty low prefix; the case q=N-2 has one "
                        + "high term. Zero e,c,A or V require no special division by "
                        + "these quantities. This theorem is finite and proves no "
                        + "signed spectral inequality. The actual partial-cell integral "
                        + "and Gram projection, analytic residue suppliers, original "
                        + "construction, infinite account, strict Robin above 5040 "
                        + "and RH remain separate obligations."))), DescribeRole.Theorem))));

    private static Formula SharpBVFormula()
    {
        var n = F.Id("N"); var d = F.Id("d"); var a = F.Id("a");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        return Disp(Seq(Forall, Sp, n, Comma, d, InMacro, Sp, naturals, Comma,
            Forall, Sp, a, InMacro, Sp, new Formula.Power(reals, naturals), Comma,
            D(0), Lt, Sp, n, Land, Sp, D(0), Lt, Sp, d, Rightarrow, Sp,
            Lvert, Sp, Call("S", n, d, a), Rvert, Sp, Le, Sp,
            new Formula.Fraction(d, D(1,6)), Cdot, Sp, Call("V", n, a)));
    }

    private static Formula TransferFormula()
    {
        var n = F.Id("N"); var q = F.Id("q"); var a = F.Id("a"); var f = F.Id("F");
        var e = F.Id("e"); var c = F.Id("c"); var m = F.Id("m"); var k = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula h = Seq(Open, q, Plus, D(1), Close);
        Formula l = Call("log", n);
        Formula Sum(Formula body) => Seq(SumToken(), Underscore, Grp(m, Eq, Sp, n),
            Caret, Grp(D(2), Cdot, Sp, n, Minus, D(1)), Sp, body);
        Formula budget = Seq(new Formula.Fraction(Seq(e, Plus, new Formula.Fraction(c, h)), l),
            Cdot, Sp, n, Cdot, Sp, Call("A", n, a), Cdot, Sp, Open,
            D(1), Plus, D(2), Cdot, Sp, Call("log", new Formula.Fraction(n, h)), Cdot, Sp,
            Open, D(1), Plus, Call("log", new Formula.Fraction(Seq(D(2), Cdot, Sp, n), h)),
            Close, Close, Plus, h, Cdot, Sp, Open,
            new Formula.Fraction(Seq(D(3), Cdot, Sp, q), D(2)), Plus, D(2), Close,
            Cdot, Sp, Call("V", n, a));
        return Disp(Seq(Forall, Sp, n, Comma, q, InMacro, Sp, naturals, Comma,
            Forall, Sp, a, Comma, f, InMacro, Sp, new Formula.Power(reals, naturals), Comma,
            Forall, Sp, e, Comma, c, InMacro, Sp, reals, Comma,
            D(3), Le, Sp, n, Land, Sp, q, Le, Sp, n, Minus, D(2), Land, Sp,
            D(0), Le, Sp, e, Land, Sp, D(0), Le, Sp, c, Land, Sp,
            Equal(Sum(Call("a", m)), D(0)), Land, Sp,
            Equal(Sum(Seq(m, Cdot, Sp, Call("a", m))), D(0)), Land, Sp,
            Open, Forall, Sp, k, InMacro, Sp, naturals, Comma, h, Le, Sp, k, Lt, Sp, n,
            Rightarrow, Sp, Lvert, Sp, Call("F", k), Minus, Call("M", k), Rvert, Sp,
            Le, Sp, e, Cdot, Sp, k, Plus, c, Close, Rightarrow, Sp,
            Lvert, Sp, Call("E", n, a), Minus, Call("Z", n, q, a, f), Rvert, Sp, Le, Sp, budget));
    }

    private static Formula SumToken() => F.Sum;
}
