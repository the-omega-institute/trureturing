using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class PadicHighDigitReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first high-digit change reconstructs a p-adic residue.",
        H("Reconstruction from a Timed High Digit"),
        Blocks(
            Paragraph(Text(
                "Fix any prime p and natural k, including zero, and put P = p^k. "
                    + "The state space is the full ring of p-adic integers. Write q for "
                    + "PadicInt.toZModPow at depth k+1 and z(x) for its canonical natural "
                    + "representative. All readings come from the single orbit x+n. "
                    + "An index n in Fin(P) ranges from zero through P-1.")),
            Describe.Lean(
                DescribeId.Create("high-digit"), DeclarationHandle.Create(Prefix + "highDigit"),
                H("The digit at depth k"), StatementSource.FromAuthor(DigitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Only the quotient by P is read; the lower remainder is not observed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("timed-word"), DeclarationHandle.Create(Prefix + "word"),
                H("The fixed consecutive reading protocol"), StatementSource.FromAuthor(WordFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The word contains exactly P readings and uses P-1 adding-one steps."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "For any positive natural P and any word w : Fin(P) to the naturals, "
                    + "let S(w) be the set of natural index values n less than P "
                    + "with w(n) different from w(0). "
                    + "The following two definitions apply to every such finite word, "
                    + "whether or not it is produced by a p-adic orbit.")),
            Describe.Lean(
                DescribeId.Create("first-change"), DeclarationHandle.Create(Prefix + "firstChange"),
                H("First change with a no-change sentinel"),
                StatementSource.FromAuthor(FirstChangeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite minimum is used when S(w) is nonempty; otherwise the "
                        + "value is P. Adjoining P to S(w) expresses the same convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("decoder"), DeclarationHandle.Create(Prefix + "decode"),
                H("A decoder using the first digit and the first change"),
                StatementSource.FromAuthor(DecoderFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first digit selects the block. Subtracting the change time "
                        + "from P recovers the position inside that block."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "In the theorem, P means p^k for the quantified p and k. For each x, "
                    + "write b for z(x) divided by P and r for z(x) modulo P. "
                    + "All quotients inside floors are natural quotients, and mod "
                    + "denotes the nonnegative natural remainder.")),
            Describe.Lean(
                DescribeId.Create("exact-reconstruction"), DeclarationHandle.Create(Prefix + "result"),
                H("Exact reconstruction and equality of observation fibers"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the window n < P, the lower remainder r+n carries at most "
                            + "once. If r is positive, the first carry occurs at P-r, "
                            + "which lies between 1 and P-1. The digit b differs from "
                            + "(b+1) mod p because p is at least two, including the "
                            + "wrap from p-1 to zero. Thus the change indices have exactly "
                            + "the lower endpoint P-r. A constant word has r equal to zero.")),
                    Paragraph(Text(
                        "The decoder identity implies that equal words have equal "
                            + "residues. Conversely, the projection is a ring homomorphism, "
                            + "so equal residues give equal digits after each natural "
                            + "translation. At k = 0, P = 1, r = 0, and the single digit "
                            + "already is the representative modulo p."))),
                DescribeRole.Theorem))));

    private static Formula P => F.Id("P");
    private static Formula Prime => F.Id("p");
    private static Formula K => F.Id("k");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula N => F.Id("n");
    private static Formula W => F.Id("w");
    private static Formula B => F.Id("b");
    private static Formula R => F.Id("r");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula States => Seq(Mathbb, Grp(F.Id("Z")), Underscore, Prime);
    private static Formula Bracket(Formula f) => Seq(Open, f, Close);
    private static Formula Digit(Formula x) => Call("d", x);
    private static Formula Word(Formula x) => Call("W", x);
    private static Formula Reading(Formula x, Formula n) => Call("W", x, n);
    private static Formula Change(Formula w) => Call("t", w);
    private static Formula Decoder(Formula w) => Call("D", w);
    private static Formula Quotient(Formula a, Formula b) => new Formula.Floor(new Formula.Fraction(a, b));
    private static Formula Modulo(Formula a, Formula b) => Call("mod", a, b);
    private static Formula WordDomain => Seq(W, Colon, Sp, Call("Fin", P), Sp, To, Sp, Naturals);
    private static Formula StateQuantifier => Seq(Forall, Sp, X, Sp, InMacro, Sp, States, Comma, Sp);
    private static Formula WordQuantifier => Seq(Forall, Sp, P, Sp, InMacro, Sp, Naturals, Comma, Sp,
        D(0), Sp, Lt, Sp, P, Sp, Rightarrow, Sp, Forall, Sp, WordDomain, Comma, Sp);

    private static Formula DigitFormula() => Disp(Seq(StateQuantifier,
        Digit(X), Sp, Eq, Sp, Quotient(Call("z", X), P), Dot));

    private static Formula WordFormula() => Disp(Seq(StateQuantifier,
        Forall, Sp, N, Sp, InMacro, Sp, Call("Fin", P), Comma, Sp,
        Reading(X, N), Sp, Eq, Sp, Digit(Seq(X, Sp, Plus, Sp, N)), Dot));

    private static Formula FirstChangeFormula() => Disp(Seq(WordQuantifier,
        Change(W), Sp, Eq, Sp, Call("min", Seq(Call("S", W), Sp, Cup, Sp,
            OpenBrace, P, CloseBrace)), Dot));

    private static Formula DecoderFormula() => Disp(Seq(WordQuantifier,
        Decoder(W), Sp, Eq, Sp, Call("w", D(0)), Sp, Cdot, Sp, P, Sp, Plus, Sp,
        Bracket(Seq(P, Sp, Minus, Sp, Change(W))), Dot));

    private static Formula ResultFormula()
    {
        Formula carry = Quotient(Seq(R, Sp, Plus, Sp, N), P);
        Formula threshold = Seq(P, Sp, Minus, Sp, R);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Prime, Comma, K, Sp, InMacro, Sp, Naturals, Comma, Sp,
                Call("Prime", Prime), Sp, Rightarrow),
            Seq(Open, StateQuantifier),
            Seq(B, Sp, Lt, Sp, Prime, Sp, Land, Sp, R, Sp, Lt, Sp, P, Sp, Land),
            Seq(Call("z", X), Sp, Eq, Sp, B, Sp, Cdot, Sp, P, Sp, Plus, Sp, R, Sp, Land),
            Seq(Reading(X, D(0)), Sp, Eq, Sp, B, Sp, Land),
            Seq(Bracket(Seq(Forall, Sp, N, Sp, InMacro, Sp, Call("Fin", P), Comma, Sp,
                Reading(X, N), Sp, Eq, Sp, Modulo(Seq(B, Sp, Plus, Sp, carry), Prime),
                Sp, Land, Sp, carry, Sp, Leq, Sp, D(1))), Sp, Land),
            Seq(Bracket(Seq(Forall, Sp, N, Sp, InMacro, Sp, Call("Fin", P), Comma, Sp,
                Bracket(Seq(Reading(X, N), Sp, Neq, Sp, B, Sp, Iff, Sp,
                    threshold, Sp, Leq, Sp, N, Sp, Land, Sp, R, Sp, Neq, Sp, D(0))))), Sp, Land),
            Seq(Change(Word(X)), Sp, Eq, Sp, threshold, Sp, Land),
            Seq(Bracket(Seq(Change(Word(X)), Sp, Eq, Sp, P, Sp, Iff, Sp, R, Sp, Eq, Sp, D(0))), Sp, Land),
            Seq(Decoder(Word(X)), Sp, Eq, Sp, Call("z", X), Close, Sp, Land),
            Seq(Bracket(Seq(Forall, Sp, X, Comma, Y, Sp, InMacro, Sp, States, Comma, Sp,
                Bracket(Seq(Word(X), Sp, Eq, Sp, Word(Y), Sp, Iff, Sp,
                    Call("q", X), Sp, Eq, Sp, Call("q", Y))))), Dot)
        ]));
    }
}
