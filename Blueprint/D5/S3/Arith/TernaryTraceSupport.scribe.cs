using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class TernaryTraceSupportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a396808");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two modulo-three support conjectures for OEIS A396808 hold at every index greater than one.",
        H("A396808: exact support modulo three"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a396808-mod-three-support"),
                DeclarationHandle.Create("D5/S3/Arith/TernaryTraceSupport.a396808_mod_three"),
                H("Complete coefficient classification"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The integer sequence a is the existing normalized solution of "
                        + "(n+1)[x^n]A^(n+1)=n[x^n]A^(n+2), with a(0)=a(1)=1. "
                        + "All quantified indices and exponents below are natural numbers. "
                        + "The cast is into ZMod(3), and ite denotes a conditional expression.")),
                    Paragraph(Text(
                        "Set t(y)=sum over r of y^(3^r). Frobenius gives t^3=t-y. "
                        + "The series U=1+y^2-t^6 equals 1+t^2+t^4 and has only even "
                        + "exponents, so U=R(y^2). Its companion roots are (t^2+t)^2 "
                        + "and (t^2-t)^2. All three satisfy z^3=z^2+y^2*z+y^4.")),
                    Paragraph(Text(
                        "Their mth-power sum is a polynomial in y^2 of degree at most "
                        + "floor(2m/3). The companion roots have order at least two. "
                        + "It follows that coefficient n of R^m vanishes when "
                        + "floor(2m/3)<n<m. This proves the reduced source equation, "
                        + "with explicit checks of its three initial indices. "
                        + "Strict-prefix coefficient induction then identifies R with a modulo three.")),
                    Paragraph(Text(
                        "A sum of two powers of three determines its sorted exponent pair "
                        + "uniquely. In the square of t, equal exponents contribute once "
                        + "and distinct exponents twice. The minus sign in U gives residues "
                        + "two and one, respectively. The two supports are disjoint: after "
                        + "cancelling a factor of three, an intersection would identify "
                        + "a diagonal exponent pair with a strictly increasing pair."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula n = F.Id("n");
        Formula r = F.Id("r");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula powers = Seq(Exists, Sp, r, Colon, Sp, naturals, Comma, Sp,
            n, Sp, Eq, Sp, new Formula.Power(D(3), r));
        Formula pairs = Seq(Exists, Sp, i, Comma, Sp, j, Colon, Sp, naturals, Comma, Sp,
            i, Sp, Lt, Sp, j, Sp, Land, Sp,
            D(2), Sp, n, Sp, Eq, Sp, D(3), Open,
            new Formula.Power(D(3), i), Sp, Plus, Sp, new Formula.Power(D(3), j), Close);
        return Disp(Seq(Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            D(1), Sp, Lt, Sp, n, Sp, Rightarrow, Sp,
            Call("cast", Call("ZMod", D(3)), Call("a", n)), Sp, Eq, Sp,
            Call("ite", powers, D(2), Call("ite", pairs, D(1), D(0)))));
    }
}
