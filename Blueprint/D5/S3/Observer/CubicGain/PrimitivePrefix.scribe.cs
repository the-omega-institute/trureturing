using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class PrimitivePrefixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual fixed-polar rank-one prefix kernel has primitive signed integer levels, including zero components.",
        H("Primitive signed levels on the whole legal prefix class"),
        Blocks(
            Paragraph(Text("A history is specified by three arbitrary finite chronological words w0,w1,w2 in the native letters M=[[0,1],[1,1]] and J=[[0,1],[1,0]]. The head of each word acts first. Its four recorded matrices are A0=I, A1=T(w0), A2=T(w1)A1 and A3=T(w2)A2. Empty words are permitted. Atoms inside a word are unread and do not change the reading index. These four indices are exactly 0,1,2,3; no word-length clock is substituted.")),
            Paragraph(Text("For a full real matrix X, the prefix quotient has components tr(Ai X)-tr(X), for i=1,2,3. With X=[[p,q],[r,s]], the coefficient row is (Ai00-1,Ai10,Ai01,Ai11-1): the offdiagonal entries are transposed by the trace pairing. Its rank is the dimension of the range of prefixMap on the full four-dimensional matrix space.")),
            Paragraph(Text("OrientedKernel(A,N) means that N is nonzero with determinant zero, that every full real matrix in the quotient kernel is a real multiple of N, and that det(S+N)-det(S)-det(N) is strictly positive for every entrywise positive determinant-zero real S. In dimension two, the first two conditions say rank one. The generator N is auxiliary and need not be integral or primitive. Actual positive sources remain the original positive rank-one sources; there is no trace normalization.")),
            Paragraph(Text("In the displayed formula A(w,i) is endpoint(w)(i), A(w) is the entire four-endpoint family, and B(A(w)) is its full trace-difference map. OK is exactly OrientedKernel as defined above. The auxiliary notation K(a,b,c,d) is signedMatrix(a,b,c,d), f(a,b) is the column (a,-b), and r(c,d) is the column (d,c). All matrix-vector equations use real casts of the integer coordinates and levels.")),
            Describe.Lean(DescribeId.Create("whole-primitive-prefix"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/PrimitivePrefix.whole_word_primitive_representation"),
                H("Whole-class representation and converse"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every three-word history and every real input generator N, the oriented-kernel condition is equivalent to rank three and the existence of nonnegative integers a,b,c,d, a positive real scale s, and integer levels m0,m1,m2,m3. Each pair (a,b) and (c,d) has gcd one; t=ac+bd is positive; N is s times the signed outer product (a,-b) transposed times (c,-d); m0=0; and every Ai sends (a,-b) transposed to that column plus mi times (d,c) transposed. Zero components in either primitive pair are included. The scale s is necessary for an arbitrary input generator.")),
                    Paragraph(Text("The positive polar on the rank-one test sources [[uv,u],[v,1]], with u,v positive, forces the diagonal entries of N to be nonnegative and its offdiagonal entries to be nonpositive. If the trace vanished, determinant zero and nonzeroness would leave a single offdiagonal direction. The actual legal endpoints would then be triangular integral unimodular matrices with both diagonal entries one. Their quotient would also annihilate a diagonal matrix, contradicting the prescribed one-dimensional kernel.")),
                    Paragraph(Text("The trace row together with the three prefix coefficient rows is therefore nonsingular. Its integer cofactors produce a nonzero integer matrix on the same real kernel line. Its orientation is chosen by the sign of the scalar relating it to N. This constructs the arithmetic generator from the original domain rather than assuming rationality, integrality or primitivity.")),
                    Paragraph(Text("A nonzero nonnegative column, chosen from the first column or the negative of the second, is divided by its gcd. Integer saturation gives the other column's integer multiplier. A second gcd extraction makes the row primitive. The saturation supplier is CofactorKernel.primitive_kernel_span, with its determinant, kernel, nonzero-sum and gcd hypotheses discharged. The same supplier, applied to (d,c), gives an integer level at every endpoint. Neither argument divides by a potentially zero primitive component.")),
                    Paragraph(Text("Conversely, the level equations put the signed outer product in the original quotient kernel. Its positive trace makes it nonzero; its determinant vanishes. Rank three makes this the whole kernel line. On a positive source its polar is bd p+bc q+ad r+ac s, which is strictly positive since the coefficients are nonnegative and ac+bd is positive. The prescribed native words supply actual cumulative legality throughout the converse.")),
                    Paragraph(Text("If a history is presented instead by its nonnegative integral unimodular endpoints, each adjacent pair A,B has an actual forward continuation exactly when BA inverse is entrywise nonnegative. Necessity follows by cancellation of the legal multiplier. For sufficiency, the inverse of an integral determinant-plus-or-minus-one matrix is integral with the same determinant sign; the legal-monoid characterization supplies a finite forward word for BA inverse. With A0=I, imposing this at the three adjacent pairs supplies the three words used in the theorem. The inverse identifies the multiplier algebraically; it is not an acquired action. Separate endpoint legality alone does not supply those transitions.")),
                    Paragraph(Text("The proof reuses LegalMatrixMonoid.legal_matrix_monoid for the exact arithmetic of native words and the pinned matrix, dimension and integer gcd APIs. It proves a representation theorem for legal prefix kernels. It does not assert global recovery, collision multiplicity, the interior normal form, or the retraction theorem."))),
                DescribeRole.Theorem))));

    private static Formula Join(Formula[] args) => args.Length switch
    {
        1 => args[0],
        2 => Seq(args[0], Comma, args[1]),
        3 => Seq(args[0], Comma, args[1], Comma, args[2]),
        4 => Seq(args[0], Comma, args[1], Comma, args[2], Comma, args[3]),
        _ => throw new System.ArgumentException("One to four arguments are used.")
    };
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(args), Close);
    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
    private static Formula Statement()
    {
        Formula w = F.Id("w"), n = F.Id("N"), a = F.Id("a"), b = F.Id("b"),
            c = F.Id("c"), d = F.Id("d"), s = F.Id("s"), m = F.Id("m"), i = F.Id("i");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var integer = Seq(Mathbb, Grp(F.Id("Z")));
        var first = Seq(OpenBrace, D(0), Comma, D(1), Comma, D(2), CloseBrace);
        var indices = Seq(OpenBrace, D(0), Comma, D(1), Comma, D(2), Comma, D(3), CloseBrace);
        var words = Seq(Open, OpenBrace, D(0), Comma, D(1), CloseBrace,
            Caret, Grp(Star), Close, Caret, Grp(first));
        var f = Call("f", a, b);
        return Disp(Seq(
            Forall, Sp, w, InMacro, Sp, words, Comma, Sp,
            Forall, Sp, n, InMacro, Sp, real, Caret, Grp(Seq(D(2), Times, D(2))), Comma, Sp,
            Call("OK", Call("A", w), n), Iff, Sp,
            Call("rank", Call("B", Call("A", w))), Eq, Sp, D(3), Land, Sp,
            Exists, Sp, a, Comma, b, Comma, c, Comma, d, InMacro, Sp, integer, Comma, Sp,
            Exists, Sp, s, InMacro, Sp, real, Comma, Sp,
            Exists, Sp, m, InMacro, Sp, integer, Caret, Grp(indices), Comma, Sp,
            D(0), Leq, Sp, a, Land, Sp, D(0), Leq, Sp, b, Land, Sp,
            D(0), Leq, Sp, c, Land, Sp, D(0), Leq, Sp, d, Land, Sp,
            Call("gcd", a, b), Eq, Sp, D(1), Land, Sp,
            Call("gcd", c, d), Eq, Sp, D(1), Land, Sp,
            D(0), Lt, Sp, a, Sp, c, Plus, b, Sp, d, Land, Sp,
            D(0), Lt, Sp, s, Land, Sp,
            n, Eq, Sp, s, Sp, Call("K", a, b, c, d), Land, Sp,
            Apply(m, D(0)), Eq, Sp, D(0), Land, Sp,
            Forall, Sp, i, InMacro, Sp, indices, Comma, Sp,
            Call("A", w, i), Sp, f, Eq, Sp, f, Plus,
            Apply(m, i), Sp, Call("r", c, d)));
    }
}
