using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FiniteTailMomentMissingWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded-degree exclusion of exact relations controls a finite sine score on a closed window.",
        H("Missing Windows from Finite Tail Moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("arbitrarily-late-tail-window"),
            DeclarationHandle.Create(Owner + ".exists_arbitrarily_late_tail_window"),
            H("A power-moment grid budget for the original time orbit"),
            StatementSource.FromAuthor(Window()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Weil/lamzouri2024effective")),
            Blocks(
                Paragraph(Text(
                    "Let J be a finite index type, let g and w be real-valued, and let each "
                    + "weight be nonnegative. The frequencies need no nonzero lower bound "
                    + "on the size of their frequency combinations. Only combinations of "
                    + "coefficient length at most 2p must avoid zero unless all coefficients "
                    + "vanish. Both h and the threshold δ are positive, and p is a positive integer.")),
                Paragraph(Text(
                    "The imaginary part of Z(t) = Σ wⱼ exp(i gⱼ t) is the sine score. "
                    + "Expand the pth powers of Z and its conjugate by the multinomial theorem. "
                    + "Two degree-p count vectors produce an integer difference with length at most "
                    + "2p. The normalized long-time integral of each nonzero character tends "
                    + "to zero by its explicit antiderivative. Thus only equal count vectors "
                    + "survive in the average of |Z|^(2p). A fixed offset of the averaging variable "
                    + "has the same limit. This is the real-time, finite-degree counterpart of "
                    + "the Fourier coefficient extraction in ExpSumCoeffEqZeroOfVanishing.lean "
                    + "in the comparison repository and the signed-frequency expansion in "
                    + "Lamzouri, Lemma 3.2.")),
                Paragraph(Text(
                    "Each diagonal term has the square of its multinomial coefficient. "
                    + "Bounding one of the factors by p! ≤ p^p and summing the remaining "
                    + "multinomial terms bounds the limit by (pV)^p. Sum the nonnegative "
                    + "moments over all grid offsets and take the average above A. If every "
                    + "candidate start had a bad grid point, its sum would be at least δ^(2p). "
                    + "The strict budget rules this out. The same start works at all grid nodes.")),
                Paragraph(Text(
                    "The floor mesh covers the closed interval, including its right endpoint. "
                    + "Moving by at most h changes the sine score by at most hB. At zero "
                    + "variance the score vanishes, and when H is negative the interval is empty. "
                    + "An arbitrary head can contribute no more than its total weight. The "
                    + "arithmetic relation hypothesis for a tail of actual ζ ordinates remains open.")),
                Paragraph(Ref("D5/S3/Fourier/Concentration/FiniteSineMissingWindow"))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Terms(Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id("j"), Sp, InMacro, Sp, F.Id("J")), Sp, body);

    private static Formula Power(Formula body, Formula exponent) => new Formula.Power(body, exponent);

    private static Formula Window()
    {
        var a = F.Id("a");
        var j = F.Id("j");
        var h = F.Id("h");
        var length = F.Id("H");
        var p = F.Id("p");
        var t = F.Id("t");
        var v = F.Id("V");
        var b = F.Id("B");
        var g = Call("g", j);
        var w = Call("w", j);
        var k = Call("k", j);
        var twoP = Multiply(D(2), p);
        var floor = Seq(new Formula.Floor(new Formula.Fraction(length, h)), Underscore, Grp(Plus));
        var ratio = new Formula.Fraction(Multiply(twoP, v), Power(DeltaLower, D(2)));
        var tailScore = Terms(Multiply(w, Call("sin", Multiply(g, t))));
        var interval = Seq(OpenBracket, a, Comma, Add(a, length), CloseBracket);
        return Disp(new Formula.Aligned([
            Seq(v, Eq, Terms(Power(w, D(2))), Comma, Quad, Sp,
                b, Eq, Terms(Multiply(w, new Formula.Absolute(g))), Comma, Quad, Sp,
                F.Id("N"), Eq, floor, Plus, D(1)),
            Seq(Forall, Sp, j, Sp, InMacro, Sp, F.Id("J"), Comma, Sp, w, Ge, D(0), Comma, Quad, Sp,
                p, Gt, D(0), Comma, Quad, Sp, h, Gt, D(0), Comma, Quad, Sp, DeltaLower, Gt, D(0)),
            Seq(Forall, Sp, F.Id("k"), Colon, Sp, F.Id("J"), To, Mathbb, Grp(F.Id("Z")),
                Comma, Quad, Sp, Terms(new Formula.Absolute(k)), Le, twoP, Quad, Sp, Land, Quad, Sp,
                Terms(Multiply(k, g)), Eq, D(0), Quad, Sp, Longrightarrow, Quad, Sp, F.Id("k"), Eq, D(0)),
            Seq(Open, v, Eq, D(0), Quad, Sp, Lor, Quad, Sp,
                Multiply(F.Id("N"), Power(Seq(Open, ratio, Close), p)), Lt, D(1), Close),
            Seq(Longrightarrow, Quad, Sp, Forall, Sp, F.Id("A"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")),
                Comma, Quad, Sp, Exists, Sp, a, Gt, F.Id("A"), Comma, Quad, Sp,
                Forall, Sp, t, Sp, InMacro, Sp, interval, Comma, Quad, Sp, tailScore,
                Lt, Add(DeltaLower, Multiply(h, b)))
        ]));
    }
}
