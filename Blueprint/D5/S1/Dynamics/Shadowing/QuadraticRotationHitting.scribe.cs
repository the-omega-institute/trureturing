using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class QuadraticRotationHittingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/QuadraticRotationHitting.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static DocumentBlock.Describe Thm(string key, string decl, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(key), DeclarationHandle.Create(Owner + decl), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit badly-approximable estimates and uniform finite hitting for scaled square-root rotations.",
        H("Quantitative Rotation Hitting"), Blocks(
        Paragraph(Text("All phases are real numbers with their integer lifts retained. Natural numbers and rounded integers in real expressions denote their canonical real coercions. Int.fract is the representative in [0,1). Mathlib supplies irrational_sqrt_two, nearest-integer rounding and the Dirichlet return theorem Real.exists_nat_abs_mul_sub_round_le. "
            + "The quantitative construction is attributed to Pro. The argument gives a uniform finite bound, including all integer lifts.")),
        Thm("scaled-sqrt-lower", "sqrt_two_scaled_round_lower", "An explicit lower approximation bound", St(
            Seq(Forall, Sp, Id("M"), Comma, Id("k"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                D(0), Lt, Id("M"), Sp, Rightarrow, Sp, D(0), Lt, Id("k"), Sp, Rightarrow),
            Seq(Seq(Frac, Grp(D(1)), Grp(Seq(Id("M"), Open, Id("M"), Plus, D(3), Close, Id("k")))), Sp, Le, Sp, Seq(Bar, Frac, Grp(Id("k"), Sqrt, Grp(D(2))), Grp(Id("M")), Minus, Call("round", Seq(Frac, Grp(Id("k"), Sqrt, Grp(D(2))), Grp(Id("M")))), Bar))),
            "Let m be the nearest integer to k sqrt(2)/M. It is nonnegative. Irrationality makes the integer 2k^2-M^2m^2 nonzero, so its absolute value is at least one. "
            + "Factor this integer as M(k sqrt(2)/M-m)(k sqrt(2)+Mm). The rounding error bounds Mm by k sqrt(2)+M/2; hence k sqrt(2)+Mm<=(M+3)k. Division yields the stated lower bound."),
        Thm("signed-mesh", "signed_rotation_mesh", "A bounded signed mesh with integer lifts", St(
            Seq(Forall, Sp, Seq(Id("theta"), Comma, Id("tau"), Comma, Id("e")), Comma, Sp, Id("e"), Neq, D(0), Sp, Rightarrow),
            Seq(Exists, Sp, Id("j"), Sp, InMacro, Sp, Id("N"), Comma, Sp, Seq(Id("j"), Bar, Id("e"), Bar), Lt, D(1), Comma),
            Seq(Exists, Sp, Id("m"), Sp, InMacro, Sp, Id("Z"), Comma, Sp, Seq(Bar, Id("theta"), Plus, Id("j"), Id("e"), Minus, Id("tau"), Minus, Id("m"), Bar), Le, Seq(Bar, Id("e"), Bar))),
            "For a positive step use j=floor(fract(tau-theta)/|e|); for a negative step use floor(fract(theta-tau)/|e|). Floor inequalities give j|e|<1 and a residual of absolute value at most |e|. "
            + "The signed integer part is kept explicitly, so the estimate includes wrap-around."),
        Thm("quarter-hitting", "badly_approximable_quarter_hitting", "Uniform hitting from a badly-approximable bound", St(
            Seq(Forall, Sp, Alpha, Comma, Kappa, Sp, InMacro, Sp, Mathbb, Grp(Id("R")), Comma, Sp,
                D(0), Lt, Kappa, Sp, Rightarrow),
            Seq(Open, Forall, Sp, Id("k"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                D(0), Lt, Id("k"), Sp, Rightarrow, Sp, Frac, Grp(Kappa), Grp(Id("k")), Le,
                Bar, Id("k"), Cdot, Alpha, Minus, Call("round", Seq(Id("k"), Cdot, Alpha)), Bar, Close, Sp, Rightarrow),
            Seq(Forall, Sp, Id("p"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp, D(0), Lt, Id("p"), Sp, Rightarrow, Sp,
                Forall, Sp, Theta, Comma, Id("a"), Sp, InMacro, Sp, Mathbb, Grp(Id("R")), Comma, Sp,
                D(0), Le, Sp, Id("a"), Sp, Rightarrow, Sp, Id("a"), Le, Frac, Grp(D(3)), Grp(D(4)), Sp, Rightarrow),
            Seq(Exists, Sp, Id("j"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                Id("j"), Le, Frac, Grp(D(2,5,6), Cdot, Sp, Id("p")), Grp(Kappa), Sp, Land, Sp,
                Call("fract", Seq(Theta, Plus, Id("j"), Cdot, Sp, Id("p"), Cdot, Alpha)), Sp, InMacro, Sp,
                OpenBracket, Id("a"), Comma, Id("a"), Plus, Frac, Grp(D(1)), Grp(D(4)), CloseBracket)),
            "Natural numbers and rounded integers in real expressions denote their canonical real coercions. Dirichlet at n=16 supplies 1<=q<=16 with beta=|qp alpha-round(qp alpha)|<=1/17. The lower approximation bound gives beta>=kappa/(qp)>0. "
            + "Aim the signed mesh at a+1/8. Its error beta stays strictly inside the quarter interval, and its integer lift identifies the correct fractional representative. "
            + "Its original index is jq<=q/beta<=q^2 p/kappa<=256p/kappa. The specialized theorem sqrt_two_scaled_quarter_hitting gives the integral bound 256 M(M+3)p.")
        )));
}
