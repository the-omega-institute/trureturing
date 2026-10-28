using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ExactTaylorObservationRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial Taylor error for bounded observations", H("Factorial Taylor error for bounded observations"), Blocks(
            Describe.Lean(DescribeId.Create("observation-taylor-norm-remainder"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ExactTaylorObservationRemainder.norm_observation_taylor_remainder"),
                H("Pointwise Taylor error"), StatementSource.FromAuthor(Pointwise()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let V be a nonzero complete normed space and W a normed space over the real or complex field. Let B:V→V and C:V→W be bounded linear maps, N a natural number, t≥0 and x∈V. No dimension restriction is imposed.")),
                    Paragraph(Text("Write b(B)=max(1,‖B‖), c(C)=‖C‖, and p(B,C,N,t,x)=the sum of t^k C(B^k x)/k! for 0≤k≤N. The exponential is the norm-convergent Banach algebra exponential.")),
                    Paragraph(Text("The factorial convolution inequality n! k!≤(n+k)! bounds the exponential series tail by r^n exp(r)/n! whenever ‖z‖≤r. Applying C and evaluating at x gives the displayed estimate without a radius restriction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("observation-taylor-energy-remainder"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ExactTaylorObservationRemainder.observation_taylor_energy_remainder"),
                H("Integrated squared Taylor error"), StatementSource.FromAuthor(Energy()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the same hypotheses, let T≥0. The squared norm is integrated with respect to ordinary Lebesgue measure on [0,T]. The result also holds at T=0.")),
                    Paragraph(Text("On this interval exp(bt)≤exp(bT). Squaring the pointwise estimate and integrating t^(2N+2) gives exactly the denominator 2N+3. Completeness is needed only for the state-space exponential, not for the scalar energy integral."))), DescribeRole.Theorem))));

    private static Formula Pointwise()
    {
        Formula n = F.Id("N"), t = F.Id("t"), x = F.Id("x"), b = App(F.Id("b"), F.Id("B")), c = Norm(F.Id("C"));
        return Disp(Seq(Prefix(), Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, t, Ge, Sp, D(0), Comma, Sp, Forall, Sp, x, InMacro, Sp, F.Id("V"), Comma, Sp,
            Norm(Seq(App(F.Id("C"), App(Seq(Exp, Open, t, F.Id("B"), Close), x)), Minus, App(F.Id("p"), F.Id("B"), F.Id("C"), n, t, x))), Le, Sp,
            Frac, Grp(c, Exp, Open, b, t, Close, Pow(Seq(Open, b, t, Close), Seq(n, Plus, D(1)))),
            Grp(Open, n, Plus, D(1), Close, Bang), Norm(x)));
    }

    private static Formula Energy()
    {
        Formula n = F.Id("N"), t = F.Id("t"), T = F.Id("T"), x = F.Id("x"), b = App(F.Id("b"), F.Id("B"));
        Formula error = Seq(App(F.Id("C"), App(Seq(Exp, Open, t, F.Id("B"), Close), x)), Minus, App(F.Id("p"), F.Id("B"), F.Id("C"), n, t, x));
        Formula coefficient = Seq(Frac, Grp(Norm(F.Id("C")), Exp, Open, b, T, Close, Pow(b, Seq(n, Plus, D(1)))), Grp(Open, n, Plus, D(1), Close, Bang));
        return Disp(Seq(Prefix(), Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, T, Ge, Sp, D(0), Comma, Sp, Forall, Sp, x, InMacro, Sp, F.Id("V"), Comma, Sp,
            Int, Underscore, Grp(D(0)), Caret, Grp(T), Pow(Norm(error), D(2)), Sp, F.Id("dt"), Le, Sp,
            Pow(Seq(Open, coefficient, Close), D(2)), Frac,
            Grp(Pow(T, Seq(D(2), n, Plus, D(3)))), Grp(D(2), n, Plus, D(3)), Pow(Norm(x), D(2))));
    }

    private static Formula Prefix()
    {
        Formula k = F.Id("K"), v = F.Id("V"), w = F.Id("W");
        return Seq(Forall, Sp, k, Comma, Sp, v, Comma, Sp, w, Comma, Sp,
            OpenBracket, App(F.Id("RCLike"), k), CloseBracket, Sp,
            OpenBracket, App(F.Id("Banach"), k, v), CloseBracket, Sp,
            OpenBracket, App(F.Id("Nonzero"), v), CloseBracket, Sp,
            OpenBracket, App(F.Id("NormedSpace"), k, w), CloseBracket, Comma, Sp,
            Forall, Sp, F.Id("B"), Colon, Sp, App(F.Id("BoundedLinearMap"), k, v, v), Comma, Sp,
            Forall, Sp, F.Id("C"), Colon, Sp, App(F.Id("BoundedLinearMap"), k, v, w), Comma, Sp);
    }

    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
}
