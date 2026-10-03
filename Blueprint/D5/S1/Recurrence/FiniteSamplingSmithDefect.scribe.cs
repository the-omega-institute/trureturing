using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FiniteSamplingSmithDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly increasing Fibonacci samples have an integral rectangular normal form and an exact modular kernel defect.",
        H("Finite Fibonacci Sampling Smith Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-fibonacci-sampling-smith-defect"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/FiniteSamplingSmithDefect.finite_sampling_smith_defect"),
                H("Fibonacci sampling has a gcd controlled Smith defect"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let m be at least two and let t : Fin(m) -> N be strictly increasing. "
                            + "The first sample index is i0 = 0, and g is the finite gcd of all "
                            + "noninitial differences t(i) - t(i0). The actual row at i is "
                            + "(Nat.fib(t(i)), Nat.fib(t(i)+1)) over Z; no abstract replacement "
                            + "matrix is used.")),
                    Paragraph(Text(
                        "The theorem supplies units U and V over the displayed rectangular integer "
                            + "matrix spaces. Their product with H is the displayed D: a 1 at "
                            + "(0,0), Nat.fib(g) at (1,1), and zero elsewhere. Nat.fib(g) is positive "
                            + "as the second factor, including the smallest admissible time configuration.")),
                    Paragraph(Text(
                        "For every positive natural modulus N, including N = 1, reduce the same "
                            + "actual matrix by Int.castRingHom into ZMod(N). Its mulVecLin kernel "
                            + "has cardinality gcd(N, Nat.fib(g)), and its mulVec is injective exactly "
                            + "when that gcd is one. The proof clears the first row, applies the "
                            + "finite Bezout column automorphism, and transports the scalar kernel "
                            + "through the unit matrices.")),
                    Paragraph(Text(
                        "The statement records the integral normal form and the modular kernel and "
                            + "injectivity consequences only; it makes no claim about a cokernel or "
                            + "free-part decomposition."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula m = F.Id("m");
        Formula t = F.Id("t");
        Formula i0 = F.Id("i0");
        Formula g = F.Id("g");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula H = F.Id("H");
        Formula Dm = F.Id("D");
        Formula Nmod = F.Id("N");
        Formula nats = Seq(Mathbb, Grp(F.Id("N")));
        Formula ints = Seq(Mathbb, Grp(F.Id("Z")));
        Formula finM = Call("Fin", m);
        Formula finTwo = Call("Fin", D(2));
        Formula fib(Formula n) => Call("fib", n);
        Formula intCast(Formula n) => Call("IntCast", n);
        Formula tAt(Formula x) => Call("t", x);
        Formula matrix(Formula rows, Formula cols, Formula scalar) =>
            Call("Matrix", rows, cols, scalar);
        Formula parenthesized(Formula value) => Seq(Open, value, Close);
        Formula Both(Formula left, Formula right) =>
            Seq(parenthesized(left), Sp, Land, Sp, parenthesized(right));
        Formula condition(Formula row, Formula col, byte rowValue, byte colValue) =>
            Both(Equal(Call("val", row), D(rowValue)), Equal(col, D(colValue)));
        Formula gDefinition = Call("gcd", Call("erase", Call("univ", finM), i0),
            Seq(F.Id("fun"), Sp, i, Sp, Rightarrow, Sp,
                Subtract(tAt(i), tAt(i0))));
        Formula hDefinition = Seq(
            F.Id("fun"), Sp, i, Sp, Rightarrow, Sp,
                Call("row", intCast(fib(tAt(i))),
                    intCast(fib(Add(tAt(i), D(1))))));
        Formula dDefinition = Seq(
            F.Id("fun"), Sp, i, Comma, Sp, j, Sp, Rightarrow, Sp,
                Call("if", condition(i, j, 0, 0), D(1),
                    Call("if", condition(i, j, 1, 1), intCast(fib(g)), D(0))));
        Formula unitsM = Call("Units", matrix(finM, finM, ints));
        Formula unitsTwo = Call("Units", matrix(finTwo, finTwo, ints));
        Formula hSpace = matrix(finM, finTwo, ints);
        Formula mapH = Call("map", H,
            Call("castRingHom", Call("ZMod", Nmod)));
        Formula kernelCard = Equal(
            Call("card", Call("ker", Call("mulVecLin", mapH))),
            Call("gcd", Nmod, fib(g)));
        Formula injective = Seq(
            Call("Injective", Call("mulVec", mapH)), Sp, Iff, Sp,
            Equal(Call("gcd", Nmod, fib(g)), D(1)));
        Formula conclusion = Seq(
            Seq(D(0), Sp, Lt, Sp, fib(g)), Sp, Land, Sp,
            Exists, Sp, F.Id("U"), Colon, Sp, unitsM, Comma, Sp,
            Exists, Sp, F.Id("V"), Colon, Sp, unitsTwo, Comma, Esc,
            Both(
                Equal(Call("mul", Call("val", F.Id("U")), H, Call("val", F.Id("V"))), Dm),
                Seq(Forall, Sp, Nmod, InMacro, Sp, nats, Comma, Sp,
                    parenthesized(Seq(
                        Seq(D(0), Sp, Lt, Sp, Nmod), Sp, Rightarrow, Sp,
                        parenthesized(Both(kernelCard, injective)))))));
        return Disp(Seq(
            Forall, Sp, m, InMacro, Sp, nats, Comma, Esc,
            Forall, Sp, t, Colon, Sp, finM, Sp, To, Sp, nats, Comma, Esc,
            parenthesized(Seq(
                Seq(D(2), Sp, Leq, Sp, m), Sp, Land, Sp,
                Call("StrictMono", t), Sp, Rightarrow, Sp,
                F.Id("let"), Sp, i0, Sp, Eq, Sp, Call("zero", finM), Comma, Sp,
                F.Id("let"), Sp, g, Sp, Eq, Sp, gDefinition, Comma, Sp,
                F.Id("let"), Sp, H, Sp, Colon, Sp, hSpace, Sp, Eq, Sp,
                hDefinition, Comma, Sp,
                F.Id("let"), Sp, Dm, Sp, Colon, Sp, hSpace, Sp, Eq, Sp,
                dDefinition, Comma, Sp,
                F.Id("in"), Sp, conclusion))));
    }
}
