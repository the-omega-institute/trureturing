using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class TildeSpectralNonconcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint-concavity classification of the tilde spectral trace.",
        H("TildeSpectralNonconcavity"), Blocks(
            Describe.Lean(DescribeId.Create("strict-first-variable-jensen-violation"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/TildeSpectralNonconcavity.strict_first_variable_jensen_violation"),
                H("Off-midpoint strict Jensen violations"),
                StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumBounds/hiai2026quasigeometric")),
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
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("joint-concavity-classification"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/TildeSpectralNonconcavity.joint_concavity_classification"),
                H("All-dimension SPD classification"),
                StatementSource.FromAuthor(Classification()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumBounds/hiai2026quasigeometric")),
                Blocks(
                    Paragraph(Text("Under 0 < alpha < 1 and p > 0, joint concavity on SPD complex matrix pairs "
                        + "simultaneously in every Fin n dimension is equivalent to alpha=1/2 and p<=1. "
                        + "The necessary direction uses strict Fin2 SPD witnesses; the equivalence is "
                        + "not asserted separately for each dimension.")),
                    Paragraph(Text("At alpha=1/2 put C=A^(p/2) B^p A^(p/2) and L=A^(-p)#_(1/2)B^p. "
                        + "The actual Riccati identity A^(p/2)L A^(p/2)=C^(1/2) and equal Gram spectral "
                        + "traces prove T=ReTr(C^(1/(2p))). Every power is CFC.rpow.")),
                    Paragraph(Text("At theta=0 the existing PsiMeanTraceConcavity.psi_jointly_concave supplies "
                        + "fixed-congruence Epstein concavity for 0<p<=1. The existing Gram and Holder/Young "
                        + "suppliers give F_p(A,B)<=(E_A(Z)+E_B((Z^(-1))*))/2 for every invertible Z. "
                        + "The optimizer Z=A^(-p/2)C^(1/4) attains equality. Selecting it at the mixed SPD "
                        + "pair and applying the fixed-Z inequalities proves generic joint concavity.")),
                    Paragraph(Text("For p>1 the positive-power Gram functional has endpoint values "
                        + "2^(-1/(2p)) at (Q,P) and (I-Q,P), and middle value 2^(-1/2) at (I/2,P), "
                        + "where Q=diag(1,0) and P is the balanced rank-one projector. Positive-power "
                        + "continuity preserves the strict gap for A0=diag(1-s,s), A1=diag(s,1-s), "
                        + "and B=(1-s)P+s(I-P), with common s in (0,1/2). The actual TILDE identity "
                        + "is used only at the SPD inputs. The middle Gram value is "
                        + "2^(-1/2)(sqrt(1-s)+sqrt(s)).")),
                    Paragraph(Text("Midpoint sufficiency is classical, including Zhang1811.01205v2. "
                        + "The retained content is the consumed formal assembly into the actual functional "
                        + "classification and the all-off-midpoint witnesses. Supported-PSD extensions, "
                        + "UNTILDE and Problem 5.18 are separate obligations. Source comparisons are "
                        + "bounded to inspected manuscripts and the pinned repository suppliers."))),
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


    private static Formula Classification()
    {
        var alpha = F.Id("alpha"); var p = F.Id("p"); var n = F.Id("n");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var natural = Seq(Mathbb, Grp(F.Id("N")));
        var matrix = Call("Matrix", Call("Fin", n), Call("Fin", n), Seq(Mathbb, Grp(F.Id("C"))));
        var spd = Call("SPD", matrix);
        var left = Seq(Forall, Sp, n, Colon, Sp, natural, Comma, Sp,
            Call("JointlyConcaveOn", spd, spd, Call("tildeTrace", alpha, p)));
        var right = Seq(alpha, Eq, new Formula.Fraction(D(1), D(2)), Land, Sp, p, Le, D(1));
        return Seq(Forall, Sp, alpha, Comma, Sp, p, Colon, Sp, real, Comma, Esc,
            Conditions(alpha, p), Implies, Esc, Open,
            Open, left, Close, Sp, Iff, Sp, Open, right, Close, Close);
    }

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
