using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class TildeSpectralNonconcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Off-midpoint nonconcavity of the tilde spectral trace.",
        H("TildeSpectralNonconcavity"), Blocks(
            Describe.Lean(DescribeId.Create("strict-first-variable-jensen-violation"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/TildeSpectralNonconcavity.strict_first_variable_jensen_violation"),
                H("Off-midpoint strict Jensen violations"),
                StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/hiai2026quasigeometric")),
                Blocks(
                    Paragraph(Text("For every 0 < alpha < 1, alpha different from one half, and p > 0, "
                        + "positive definite complex 2 by 2 matrices A, C and one common B violate "
                        + "first-variable concavity at a real weight theta in (0,1).")),
                    Paragraph(Text("The base-first geometric mean is X^(1/2) (X^(-1/2) Y X^(-1/2))^alpha X^(1/2). "
                        + "Put K=A^(-p) #_alpha B^p. The actual functional is the real trace of "
                        + "(K^(1/2) A^(2p(1-alpha)) K^(1/2))^(1/p). Every matrix power is CFC.rpow. "
                        + "The same generic definition is used for every finite dimension.")),
                    Paragraph(Text("Let r=1-alpha, gamma=(3/2)^r, eta=4^r, "
                        + "delta=(gamma-1)/(2(eta-gamma)), q=delta^(1/(2r-1)), and w=1/(1+q). "
                        + "The normalized rank-one projector has diagonal entries w and 1-w and "
                        + "off-diagonal entries sqrt(w(1-w)). For A_x=diag(x,1), set "
                        + "mu=1-w+w x^p and nu=1-w+w x^(2pr). Normalized rank-one compression gives "
                        + "K=mu^(-r) P and T(A_x,P)=(mu^(-r) nu)^(1/p). "
                        + "The existing two_point_cfc supplier evaluates the actual matrix powers.")),
                    Paragraph(Text("With a=q^(1/p), b=(2q)^(1/p), the exact difference of the scalar "
                        + "cores is (1-w)^alpha (gamma-1)/(2 3^r)>0. This works for both signs of "
                        + "2r-1. Set theta=(h(a)-h(b))/(2h(a)) and c=a+(b-a)/theta. "
                        + "Then b=(1-theta)a+theta c and positivity of h(c) gives a strict Jensen gap. "
                        + "Continuity of positive matrix powers at the three fixed SPD first inputs "
                        + "preserves that gap for one common SPD B=P+epsilon I. "
                        + "No negative power is applied to the singular projector."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Conditions(Formula alpha, Formula p) =>
        Seq(D(0), Lt, alpha, Land, Sp, alpha, Lt, D(1), Land, Sp, D(0), Lt, p);

    private static Formula Endpoint()
    {
        var alpha = F.Id("alpha"); var p = F.Id("p"); var theta = F.Id("theta");
        var a = F.Id("A"); var c = F.Id("C"); var b = F.Id("B");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var matrix = Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Seq(Mathbb, Grp(F.Id("C"))));
        var mix = Seq(Open, D(1), Minus, theta, Close, a, Plus, theta, c);
        return Seq(Forall, Sp, alpha, Comma, Sp, p, Colon, Sp, real, Comma, Esc,
            Conditions(alpha, p), Land, Sp, alpha, Neq, new Formula.Fraction(D(1), D(2)), Implies, Esc,
            Exists, Sp, a, Comma, Sp, c, Comma, Sp, b, Colon, Sp, matrix, Comma, Esc,
            Call("PosDef", a), Land, Sp, Call("PosDef", c), Land, Sp, Call("PosDef", b), Land, Sp,
            Exists, Sp, theta, Colon, Sp, real, Comma, Esc,
            D(0), Lt, theta, Land, Sp, theta, Lt, D(1), Land, Esc,
            Call("tildeTrace", alpha, p, mix, b), Lt,
            Seq(Open, D(1), Minus, theta, Close, Call("tildeTrace", alpha, p, a, b)),
            Plus, theta, Call("tildeTrace", alpha, p, c, b));
    }
}
