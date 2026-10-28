using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class PrefixKernelSignsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positively oriented rank-one legal-prefix kernel has signed entries, positive trace and an invertible full trace map.",
        H("Signs and positive trace on the whole prefix class"),
        Blocks(
            Paragraph(Text("Mat is the entire real 2 by 2 matrix space. A triple w:Fin 3 -> List Bool consists of three arbitrary finite chronological multipliers, including empty lists. The existing futureProduct uses false for M=[[0,1],[1,1]] and true for J=[[0,1],[1,0]], with the head acting first. The word at clock i is the concatenation of the first i lists of w. Its actual matrix is A_i=prefixMatrix(w,i), for the original indices i=0,1,2,3. Thus A_0=I and A_(i+1)=futureProduct(w_i) A_i. Word lengths and entries are unbounded.")),
            Paragraph(Text("The linear operators are B_pre(X)_i=trace(A_(i+1)X)-trace(X), with i in Fin 3, and L_pre(X)_i=trace(A_i X), with i in Fin 4. The determinant polar is b(X,Y)=det(X+Y)-det(X)-det(Y). A strictly positive rank-one matrix has all four entries strictly positive and actual matrix rank one.")),
            Paragraph(Text("Write G_+(w,N) for OrientedKernelGenerator(w,N). It requires N nonzero of rank one, B_pre(X)=0 if and only if X=vN for some real v, for every full real matrix X, and b(S,N)>0 for every strictly positive rank-one S. It assumes no entry signs, trace positivity or injectivity. This is an arbitrary positive orientation of the kernel generator in the whole class G; zero entries of N and empty multipliers remain included.")),
            Describe.Lean(DescribeId.Create("prefix-kernel-signs-positive-trace-invertible"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/PrefixKernelSigns.kernel_signs_positive_trace_invertible"),
                H("The full sign, trace and invertibility theorem"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every triple w and every full real matrix N satisfying G_+(w,N), both diagonal entries of N are nonnegative, both off-diagonal entries are nonpositive, its trace is strictly positive, and L_pre is bijective from Mat onto all real four-vectors. Bijectivity of this linear map gives a linear inverse on the full four-dimensional space, without a positive-source restriction.")),
                    Paragraph(Text("For u,v>0, the test matrix [[uv,u],[v,1]] is strictly positive of rank one, being the outer product of (u,1) and (v,1). Its polar with N is (N00-N10*u)+(N11*u-N01)*v. An affine function nonnegative on the positive half-line has nonnegative intercept and slope: a negative slope gives a sufficiently large explicit counterexample, and a negative intercept gives a sufficiently small one. Apply this first in v, then separately to the two resulting affine functions in u. This yields all four entry signs.")),
                    Paragraph(Text("If the trace were nonpositive, the nonnegative diagonal entries would both vanish. N is nonzero, so at least one off-diagonal entry is strictly negative. Each endpoint is entrywise nonnegative by the legal matrix monoid theorem. Its level equation is A01*N10+A10*N01=0, a sum of nonpositive terms. The strictly negative entry forces one corresponding endpoint off-diagonal entry to vanish. Thus every endpoint is triangular. Its nonnegative integral diagonal entries have product one, since its determinant is plus or minus one; hence both diagonal entries are one.")),
                    Paragraph(Text("The matrix E00=[[1,0],[0,0]] then lies in the prefix-difference kernel. It cannot be a scalar multiple of N, since N00=0 but E00_00=1. This contradicts the kernel-line condition and proves positive trace. This exclusion uses the sign pattern, nonzero generator and kernel-line condition; the rank-one generator assumption is retained in G_+ but is not needed in this step.")),
                    Paragraph(Text("If all four prefix traces of X vanish, the identity reading at the unchanged index zero gives trace(X)=0. The remaining three readings put X in the prefix-difference kernel, so X=vN. Positive trace of N forces v=0. Therefore L_pre is injective. Its source and target each have real dimension four, so the finite-dimensional injectivity-surjectivity theorem gives bijectivity. Primitive integer normal forms and later structural conclusions require additional arguments."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, Formula x) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, x, Close);
    private static Formula Entry(byte i, byte j) =>
        Seq(F.Id("N"), Underscore, Grp(Seq(D(i), D(j))));
    private static Formula Statement()
    {
        var w = F.Id("w"); var n = F.Id("N");
        var words = Seq(OpenBrace, D(0), Comma, D(1), CloseBrace, Caret, Grp(Star));
        var matrices = Seq(Mathbb, Grp(F.Id("R")), Caret, Grp(Seq(D(2), Times, D(2))));
        return Disp(Seq(
            Forall, Sp, w, InMacro, Sp, Open, words, Close, Caret, Grp(D(3)), Comma, Sp,
            Forall, Sp, n, InMacro, Sp, matrices, Comma, Sp,
            F.Id("G"), Underscore, Grp(Plus), Open, w, Comma, n, Close, Implies, Sp,
            Open, D(0), Leq, Sp, Entry(0,0), Land, Sp,
            D(0), Leq, Sp, Entry(1,1), Land, Sp,
            Entry(0,1), Leq, Sp, D(0), Land, Sp,
            Entry(1,0), Leq, Sp, D(0), Close, Land, Sp,
            D(0), Lt, Sp, Call("tr", n), Land, Sp,
            Call("Bijective", Seq(F.Id("L"), Underscore, Grp(F.Id("pre")), Open, w, Close))));
    }
}
