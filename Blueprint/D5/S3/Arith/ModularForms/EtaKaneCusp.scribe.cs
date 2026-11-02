using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EtaKaneCuspDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/mathlib2026etacusps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant cusp multipliers with exact eta and reciprocal Euler normalization.",
        H("EtaKaneCusp"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kane-one-third"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaKaneCusp.kane_one_third"),
                H("The actual Euler quotient phase"),
                StatementSource.FromAuthor(Disp(Seq(Call("H", F.Id("q")), Sp, Eq, Sp, Call("exp", Seq(Minus, Div(Seq(Pi, F.Id("i")), D(9)))), Sp, Cdot, Sp, Div(D(1), Call("sqrt", Div(Seq(D(3), F.Id("w")), Seq(D(2), Pi)))), Sp, Cdot, Sp, Call("exp", Seq(Div(Pow(Pi, D(2)), Seq(D(5,4), F.Id("w"))), Minus, Div(F.Id("w"), D(2,4)))), Sp, Cdot, Sp, Call("H", F.Id("u"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every Re(w)>0, H(exp(2*pi*i/3-w))=exp(-pi*i/9) sqrt(3*w/(2*pi))^-1 exp(pi^2/(54*w)-w/24) H(exp(-2*pi*i/3-4*pi^2/(9*w))), where H(q)=E(q)^2/E(q^3).")),
                    Paragraph(Text("Rewrite H as P(q^3)/P(q)^2, apply the exact zero-cusp formula at 3w and the one-third formula at w, and cancel nonzero factors. The cubic exponential normalization is proved explicitly. The displayed reciprocal principal root is valid on the entire right half-plane. This component is classical analytic infrastructure for Kane's circle method. Farey arcs, Hankel evaluation, circle bounds, coefficient recurrence, signs and smoothing remain unpaid; the full denominator-ten target is not asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kane-two-thirds"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaKaneCusp.kane_two_thirds"),
                H("Conjugate Euler quotient phase"),
                StatementSource.FromAuthor(Disp(Seq(Call("H", F.Id("q")), Sp, Eq, Sp,
                    Call("exp", Div(Seq(Pi, F.Id("i")), D(9))), Sp, Cdot, Sp,
                    Div(D(1), Call("sqrt", Div(Seq(D(3), F.Id("w")), Seq(D(2), Pi)))),
                    Sp, Cdot, Sp, Call("exp", Seq(Div(Pow(Pi, D(2)), Seq(D(5,4), F.Id("w"))),
                        Minus, Div(F.Id("w"), D(2,4)))), Sp, Cdot, Sp, Call("H", F.Id("u"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every Re(w)>0 take q=exp(4*pi*i/3-w) and u=exp(2*pi*i/3-4*pi^2/(9*w)). The phase is exp(pi*i/9), with the same reciprocal principal root and exponential shift. The representative -1/3 equals the 2/3 cusp by periodicity of the exponential. Conjugation of the actual Euler product and its entire-domain one-third identity proves this equality. The Fourier phase sum in EtaCuspPhases uses exactly these two H multipliers."))),
                DescribeRole.Theorem))));

    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
