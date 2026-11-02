using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EtaCuspPhasesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/mathlib2026etacusps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant cusp multipliers with exact eta and reciprocal Euler normalization.",
        H("EtaCuspPhases"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partition-two-thirds"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaCuspPhases.partition_two_thirds"),
                H("Conjugate partition phase"),
                StatementSource.FromAuthor(Disp(Seq(Call("P", F.Id("q")), Sp, Eq, Sp, Call("exp", Seq(Minus, Div(Seq(Pi, F.Id("i")), D(1,8)))), Sp, Cdot, Sp, Call("sqrt", Div(Seq(D(3), F.Id("w")), Seq(D(2), Pi))), Sp, Cdot, Sp, Call("exp", Seq(Div(Pow(Pi, D(2)), Seq(D(5,4), F.Id("w"))), Minus, Div(F.Id("w"), D(2,4)))), Sp, Cdot, Sp, Call("P", F.Id("u"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every Re(w)>0, the reciprocal partition transform at exp(4*pi*i/3-w), the two-thirds cusp, has phase exp(-pi*i/18), the same principal root sqrt(3*w/(2*pi)), and transformed point exp(2*pi*i/3-4*pi^2/(9*w)).")),
                    Paragraph(Text("Conjugation commutes with the Euler product and with the principal square root on the right half-plane. Conjugating the one-third identity at conjugate(w) therefore proves the entire-domain equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partition-zero"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaCuspPhases.partition_zero"),
                H("The denominator-one phase is one"),
                StatementSource.FromAuthor(Disp(Seq(Call("P", Call("exp", Seq(Minus, F.Id("w")))), Sp, Eq, Sp, Call("sqrt", Div(F.Id("w"), Seq(D(2), Pi))), Sp, Cdot, Sp, Call("exp", Seq(Div(Pow(Pi, D(2)), Seq(D(6), F.Id("w"))), Minus, Div(F.Id("w"), D(2,4)))), Sp, Cdot, Sp, Call("P", Call("exp", Seq(Minus, Div(Seq(D(4), Pow(Pi, D(2))), F.Id("w")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every Re(w)>0, P(exp(-w))=sqrt(w/(2*pi)) exp(pi^2/(6*w)-w/24) P(exp(-4*pi^2/w)).")),
                    Paragraph(Text("The existing eta inversion theorem determines the exact multiplier, and eta-to-partition normalization cancels sqrt(i). No root-of-unity choice is left."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-phase-sum"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaCuspPhases.first_phase_sum"),
                H("The first Fourier phase sum"),
                StatementSource.FromAuthor(Disp(Seq(Call("A", D(1), F.Id("n")), Sp, Eq, Sp, D(2), Sp, Cdot, Sp, Call("cos", Seq(Div(Seq(D(2), Pi, F.Id("n")), D(3)), Plus, Div(Pi, D(9))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural n, exp(-pi*i/9) exp(-2*pi*i*n/3)+exp(pi*i/9) exp(-4*pi*i*n/3)=2*cos(2*pi*n/3+pi/9).")),
                    Paragraph(Text("Integer exponential periodicity and the two-exponential cosine identity preserve the original negative Fourier-extraction exponents. This identity alone is not a coefficient-sign theorem."))),
                DescribeRole.Theorem))));

    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
