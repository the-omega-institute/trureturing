using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EtaThirdCuspDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/mathlib2026etacusps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant cusp multipliers with exact eta and reciprocal Euler normalization.",
        H("EtaThirdCusp"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eta-third-cusp"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaThirdCusp.eta_third_cusp"),
                H("ST cubed S fixes the eta phase"),
                StatementSource.FromAuthor(Disp(Seq(Call("eta", Call("act", Gamma, Tau)), Sp, Eq, Sp, Call("exp", Seq(Minus, Div(Seq(Pi, F.Id("i")), D(4)))), Sp, Cdot, Sp, Call("sqrt", Seq(D(3), Tau, Minus, D(1))), Sp, Cdot, Sp, Call("eta", Tau)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every tau in the upper half-plane, eta(gamma tau)=exp(-pi*i/4) sqrt(3*tau-1) eta(tau), where gamma=[-1,0;3,-1]=ST^3S and the root is principal.")),
                    Paragraph(Text("Constancy permits evaluation at tau=i. Eta inversion at 3+i and translation by three determine xi=(sqrt(i))^-1=exp(-pi*i/4). The right-half-plane principal-root calculation removes the branch ambiguity; the resulting equality holds for all tau."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partition-one-third"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaThirdCusp.partition_one_third"),
                H("Exact partition phase at one third"),
                StatementSource.FromAuthor(Disp(Seq(Call("P", F.Id("q")), Sp, Eq, Sp, Call("exp", Div(Seq(Pi, F.Id("i")), D(1,8))), Sp, Cdot, Sp, Call("sqrt", Div(Seq(D(3), F.Id("w")), Seq(D(2), Pi))), Sp, Cdot, Sp, Call("exp", Seq(Div(Pow(Pi, D(2)), Seq(D(5,4), F.Id("w"))), Minus, Div(F.Id("w"), D(2,4)))), Sp, Cdot, Sp, Call("P", F.Id("u"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every Re(w)>0, P(exp(2*pi*i/3-w))=exp(pi*i/18) sqrt(3*w/(2*pi)) exp(pi^2/(54*w)-w/24) P(exp(-2*pi*i/3-4*pi^2/(9*w))).")),
                    Paragraph(Text("The explicit eta-to-P shift supplies the normalized phase exp(pi*i/18). It is distinct from the eta multiplier exp(-pi*i/4); the distinction is necessary for the subsequent Euler quotient."))),
                DescribeRole.Theorem))));

    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
