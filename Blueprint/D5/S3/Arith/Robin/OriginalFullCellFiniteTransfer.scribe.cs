using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalFullCellFiniteTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.";
    private static DocumentBlock Def(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("original-full-cell-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full nonnegative coefficients admit finite actual Mobius transport with the complete integer mean and pole-centered prefix.",
        H("Full Positive Cell Finite Transfer"),
        Blocks(
            Paragraph(Text("All logarithms are natural. The block is N<=m<2*N, with natural N>=3. "
                + "The coefficients b are arbitrary nonnegative real numbers on this entire block. "
                + "There is no zeroth- or first-moment cancellation. The response and variation are "
                + "the original OriginalResidualFiniteTransfer definitions. The constant response, "
                + "the same actual Mobius coefficient in its linear and floor pieces, every "
                + "prime-power index and both jumps of the zero extension are retained.")),
            Def("totalMass", "The full mass",
                "For every natural N and real sequence b, A(N,b)=sum(N<=m<2*N,b(m))."),
            Def("firstMoment", "The full first moment",
                "For every N,b, B(N,b)=sum(N<=m<2*N,m*b(m)). For nonnegative b, 0<=B<=2*N*A."),
            Def("fracPair", "The positive fractional kernel",
                "For every natural N,d and b, Q(N,b,d)=sum(N<=m<2*N,b(m)*(m mod d)/d). "
                + "Mathlib's Int.fract_div_natCast_eq_div_natCast_mod identifies this remainder "
                + "quotient with the literal fractional part of the real quotient m/d."),
            Def("logPair", "The full logarithmic kernel",
                "For every N,b,d, K(N,b,d)=log(N/d)*Q(N,b,d). At positive N, K(N,b,N)=0; "
                + "integer remainders also give K(N,b,1)=0."),
            Def("logDifference", "Consecutive full-kernel difference",
                "For every N,b,k, D(N,b,k)=K(N,b,k)-K(N,b,k+1)."),
            Def("weightedVariation", "Weighted full-kernel variation",
                "For every N,h,b, W(N,h,b)=sum(h<=k<N,k*abs(D(N,b,k)))."),
            Def("pairing", "The unchanged full response pairing",
                "For every N,b, E(N,b)=sum(N<=m<2*N,b(m)*response(N,m)). "
                + "The original affine-and-floor response is used directly."),
            Def("replacement", "Positive high-prefix replacement",
                "For every N,q,b,F, Z(N,q,b,F)=sum(q+1<=k<N,(F(k)+2)*D(N,b,k))/log N. "
                + "The sign is positive. The literal +2 telescopes to 2*K(N,b,q+1)/log N."),
            Def("polePrefix", "The exact pole-centered low prefix",
                "For every natural q put h=q+1. R(q)=sum(1<=d<=q,mu(d)*log(h/d))+2*log h, "
                + "with the actual Mobius function and inclusive finite cutoff."),
            Def("reciprocalPrefix", "The exact reciprocal low prefix",
                "For all natural N,q, U(N,q)=sum(1<=d<=q,mu(d)*log(N/d)/d)."),
            Def("meanCorrection", "The entire nonzero-mean correction",
                "For every N,q,b, put h=q+1, u=log(N/h), L=log N. "
                + "C(N,q,b)=A(N,b)/(2*L)*(R(q)-U(N,q)+(M(q)+2)*u/h). "
                + "M(q) is the unchanged actual inclusive Mobius prefix."),
            Describe.Lean(DescribeId.Create("original-full-cell-finite-transfer"),
                DeclarationHandle.Create(Prefix + "originalFullCell_finite_transfer"),
                H("Finite full-positive transfer"), StatementSource.FromAuthor(TransferFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For natural N>=3 and q<=N-2, arbitrary real sequences b,F "
                        + "and real e,c>=0, assume b(m)>=0 on N<=m<2*N and "
                        + "abs(F(k)-M(k))<=e*k+c on h=q+1<=k<N. Set u=log(N/h), "
                        + "v=log(2*N/h), L=log N and V=variation(N,b). Then "
                        + "abs(E-Z-C)<=((e+c/h)/L)*N*A*(1+2*u^2+2*u*(1+v))"
                        + "+h*(3*q/2+2)*V.")),
                    Paragraph(Text("Natural division and finite exchange give E=A+sum(mu(d)*K(d))/L. "
                        + "The public ActualOddMobiusFinitePairing.prefix_abel supplies its positive "
                        + "Abel form. K(N)=0 retains the exact terminal boundary. In the full kernel, "
                        + "Q(k)-Q(k+1)=B/(k*(k+1))-sum(b(m)*(floor(m/k)-floor(m/(k+1)))). "
                        + "The three product-difference costs are 2*N*A*u^2, 2*N*A*u*(1+v) and N*A. "
                        + "The original weighted_floor_bound, reciprocal_log_step and weighted_log_step "
                        + "supply the finite count and logarithmic estimates.")),
                    Paragraph(Text("Let S(d)=sum(b(m)*centered(d,m)). The exact integer mean gives "
                        + "Q(d)=A*(d-1)/(2*d)+S(d). The original-owner centered_pair_variation_bound "
                        + "gives abs(S(d))<=d*V with both jumps and no moment hypotheses. "
                        + "Writing P=sum(1<=k<=q,M(k)*D(k)), the exact low identity is "
                        + "A+(P-2*K(h))/L=C+[sum(1<=d<=q,mu(d)*log(N/d)*S(d))"
                        + "-(M(q)+2)*u*S(h)]/L. The truncated pole payment is literally -2*K(h)/L. "
                        + "The centered remainder costs at most h*(3*q/2+2)*V, using "
                        + "sum(1<=d<=q,d)=q*(q+1)/2 and abs(M(q)+2)<=q+2.")),
                    Paragraph(Text("The remaining high error is exactly "
                        + "sum(h<=k<N,(M(k)-F(k))*D(k))/L. The shared original-owner "
                        + "prefix_error_bound bounds it by ((e+c/h)/L)*W. At q=0, "
                        + "R=U=M(0)=0, h=1 and u=L, so C=A exactly. At q=N-2 the high range "
                        + "contains only k=N-1. Zero coefficients, variation or error constants "
                        + "require no division by them. Full residues, a signed infinite account, "
                        + "strict Robin above 5040 and RH remain open."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-full-cell-finite-transfer-sharp"),
                DeclarationHandle.Create(Prefix + "originalFullCell_finite_transfer_sharp"),
                H("Sharp finite full-positive transfer"), StatementSource.FromAuthor(TransferFormula(true)),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under exactly the same full-positive hypotheses, define "
                        + "B(N,q,b)=0 if q=0, and B(N,q,b)=h*(3*q/2+2)*V/16 otherwise, h=q+1. "
                        + "The sharp bound is abs(E-Z-C)<=((e+c/h)/L)*N*A*(1+2*u^2+2*u*(1+v))+B. "
                        + "The complete block, nonnegative b, e,c>=0, actual F prefix-error "
                        + "hypothesis and full range 0<=q<=N-2 are unchanged.")),
                    Paragraph(Text("The original-owner centered_pair_variation_sharp_bound supplies "
                        + "abs(S(d))<=d*V/16. Shared private centered-log and low-error sums consume "
                        + "this estimate with V/16, using all actual Mobius indices and the literal +2. "
                        + "At q=0 the low error is exactly zero because centered(1,m)=0; "
                        + "the mean remains C(N,0,b)=A(N,b) for N>1. Neither the high error "
                        + "nor the mean is discarded. Both public transfers call the same exact "
                        + "decomposition and final error assembly, retaining PLUS replacement, "
                        + "the literal -2*K(h)/L, the full first moment and the high nonnegativity "
                        + "requirement. No sign is assumed for Abel differences.")),
                    Paragraph(Text("For actual partial cells take b(m)=log(N)*omega(a,b,m), "
                        + "N<=a<=b<=2*N. OriginalResidualPartialCellWeights supplies nonnegativity, "
                        + "A=log(N)*(g(a)-g(b)) and V<=2*log(N)*activationDensity(a) "
                        + "through its original private mass and variation proofs. These are "
                        + "applications of the finite theorem, with no vanishing first moment. "
                        + "The primitive estimate also covers N=1; the logarithmic transfer keeps "
                        + "N>=3. Signed MAIN, strict Robin above 5040, cofinal/global transport "
                        + "and RH remain open."))), DescribeRole.Theorem))));

    private static Formula TransferFormula(bool sharp = false)
    {
        var n = F.Id("N"); var q = F.Id("q"); var b = F.Id("b"); var f = F.Id("F");
        var e = F.Id("e"); var c = F.Id("c"); var m = F.Id("m"); var k = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula h = Seq(Open, q, Plus, D(1), Close);
        Formula u = Call("log", new Formula.Fraction(n, h));
        Formula v = Call("log", new Formula.Fraction(Seq(D(2), Cdot, Sp, n), h));
        Formula low = Seq(h, Cdot, Sp, Open,
            new Formula.Fraction(Seq(D(3), Cdot, Sp, q), D(2)),
            Plus, D(2), Close, Cdot, Sp, Call("V", n, b));
        if (sharp) low = Call("B", n, q, b);
        Formula budget = Seq(new Formula.Fraction(Seq(e, Plus, new Formula.Fraction(c, h)), Call("log", n)),
            Cdot, Sp, n, Cdot, Sp, Call("A", n, b), Cdot, Sp, Open,
            D(1), Plus, D(2), Cdot, Sp, new Formula.Power(u, D(2)), Plus,
            D(2), Cdot, Sp, u, Cdot, Sp, Open, D(1), Plus, v, Close, Close,
            Plus, low);
        return Disp(Seq(Forall, Sp, n, Comma, q, InMacro, Sp, naturals, Comma,
            Forall, Sp, b, Comma, f, InMacro, Sp, new Formula.Power(reals, naturals), Comma,
            Forall, Sp, e, Comma, c, InMacro, Sp, reals, Comma,
            D(3), Le, Sp, n, Land, Sp, q, Le, Sp, n, Minus, D(2), Land, Sp,
            D(0), Le, Sp, e, Land, Sp, D(0), Le, Sp, c, Land, Sp,
            Open, Forall, Sp, m, InMacro, Sp, naturals, Comma, n, Le, Sp, m, Lt, Sp,
            D(2), Cdot, Sp, n, Rightarrow, Sp, D(0), Le, Sp, Call("b", m), Close, Land, Sp,
            Open, Forall, Sp, k, InMacro, Sp, naturals, Comma, h, Le, Sp, k, Lt, Sp, n,
            Rightarrow, Sp, Lvert, Sp, Call("F", k), Minus, Call("M", k), Rvert, Sp,
            Le, Sp, e, Cdot, Sp, k, Plus, c, Close, Rightarrow, Sp,
            Lvert, Sp, Call("E", n, b), Minus, Call("Z", n, q, b, f), Minus,
            Call("C", n, q, b), Rvert, Sp, Le, Sp, budget));
    }
}
