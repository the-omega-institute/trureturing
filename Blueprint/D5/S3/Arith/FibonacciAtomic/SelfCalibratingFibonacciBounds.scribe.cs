using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SelfCalibratingFibonacciBoundsDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Packet()
    {
        Formula n = F.Id("n"), delta = F.Id("delta");
        Formula fn = Call("F", n), kn = Call("K", n);
        Formula mn = Call("m", n), qn = Call("q", n);
        Formula bounds = Seq(Forall, Sp, F.Id("w"), Comma, Sp,
            F.Id("b"), Sp, Leq, Sp, fn, Sp, Land, Sp,
            F.Id("c"), Sp, Leq, Sp, fn, Sp, Land, Sp,
            Vert, Sp, delta, Vert, Sp, Leq, Sp, fn, Sp, Land, Sp,
            Minus, delta, Sp, Leq, Sp, kn, Sp, Land, Sp,
            delta, Minus, D(2), F.Id("b"), Sp, Leq, Sp, kn);
        Formula common = Seq(Forall, Sp, n, Sp, Geq, Sp, D(1), Comma, Sp,
            Call("length", mn), Eq, n, Sp, Land, Sp,
            Call("b", mn), Eq, fn, Sp, Land, Sp,
            Call("c", mn), Eq, fn, Sp, Land, Sp,
            Vert, Call("delta", mn), Vert, Eq, fn);
        Formula conjugate = Seq(Forall, Sp, n, Sp, Geq, Sp, D(3), Comma, Sp,
            Call("length", qn), Eq, n, Sp, Land, Sp,
            Minus, Call("delta", qn), Eq, kn);
        return Disp(Seq(Open, bounds, Close, Sp, Land, Sp,
            Open, common, Close, Sp, Land, Sp, Open, conjugate, Close));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every literal Fibonacci and swap word obeys five Fibonacci bounds with explicit sharpness words.",
        H("Sharp Fibonacci Bounds for Literal Matrix Words"),
        Blocks(
            Paragraph(Text(
                "Let M have rows (0,1),(1,1), and let J have rows (0,1),(1,0). "
                + "A finite Boolean list w is read chronologically, with false denoting M and true "
                + "denoting J. Its matrix E(w) satisfies E(empty)=I and E(p followed by q)=E(q)E(p). "
                + "Write E(w) with rows (a,b),(c,d), set delta=d-a, and let n be the literal list length.")),
            Paragraph(Text(
                "The Fibonacci sequence has F(0)=0, F(1)=1 and F(n+2)=F(n)+F(n+1). "
                + "Set K(n)=F(n-2), where subtraction of natural numbers is truncated at zero. "
                + "Thus K(n)=0 for n=0,1,2. All matrix entries and comparisons are integers.")),
            Paragraph(Text(
                "For each natural n define the lists m(n)=replicate(n,false) and "
                + "q(n)=[true] followed by replicate(n-2,false) followed by [true]. "
                + "The functions b(v), c(v), and delta(v) read the corresponding entries "
                + "and diagonal difference of E(v). In the first conjunct n=length(w).")),
            Describe.Lean(DescribeId.Create("self-calibrating-raw-word-fibonacci-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/SelfCalibratingFibonacciBounds.raw_word_fibonacci_bounds"),
                H("Five universal inequalities and two exact word families"),
                StatementSource.FromAuthor(Packet()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every raw list is included: the empty list, lengths 1,2,3,4, and lists "
                        + "with arbitrary adjacent JJ pairs. The bound uses the length before any "
                        + "pair is removed.")),
                    Paragraph(Text(
                        "For every n>=1 the single list "
                        + "v=replicate(n,false) has length n and simultaneously satisfies "
                        + "b(v)=F(n), c(v)=F(n), and abs(delta(v))=F(n). Its matrix is M to the "
                        + "power n, with rows (F(n-1),F(n)),(F(n),F(n-1)+F(n)).")),
                    Paragraph(Text(
                        "For every n>=3 the literal list "
                        + "v=[true] followed by replicate(n-2,false) followed by [true] has "
                        + "length n and satisfies -delta(v)=F(n-2)=K(n). Its matrix is "
                        + "J M to the power n-2 J. No equality for delta-2b at every length is asserted.")),
                    Paragraph(Text(
                        "A joint strong induction treats the two offdiagonal entries and four "
                        + "linear signed inequalities. A JJ pair leaves the matrix unchanged and "
                        + "reduces the length by two; monotonicity of F and K then gives the "
                        + "bounds at the original length. An MM pair uses M squared=M+I, so its "
                        + "matrix is the sum of word matrices of lengths n-1 and n-2. The linear "
                        + "inequalities add, F(n-1)+F(n-2)=F(n), and "
                        + "K(n-1)+K(n-2)<=K(n), including n=2,3,4.")),
                    Paragraph(Text(
                        "Without an equal adjacent pair the word alternates. At even length 2j "
                        + "the matrices have rows (1,j),(0,1) or (1,0),(j,1). At odd length 2j+1 "
                        + "they have rows (0,1),(1,j+1) or (j,1),(1,0). The estimates "
                        + "j<=F(2j-1) and j+1<=F(2j+1) give all remaining bounds, including j=0. "
                        + "The two bounds on delta give the absolute value bound."))),
                DescribeRole.Theorem))));
}
