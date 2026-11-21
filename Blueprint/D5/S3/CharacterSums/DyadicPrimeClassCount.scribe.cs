using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DyadicPrimeClassCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic prime counts from two relative Chebotarev estimates",
        H("Effective prime counts in a varying residue class"),
        Blocks(
            Paragraph(Text("Write P(m,a;l,u) for the number of primes congruent to a modulo m in (l,u]. "
                + "Let Li(t) be the integral of 1/log u from 2 to t, and set F(t) = Li(t) − θ Li(tᵝ). "
                + "For a relative tolerance ε define M(ε,Y) = max(0, Y/log(2Y) − 24εY/log Y).")),
            Paragraph(Text("Write S(θ,β,Q,s) for the following conditions. The sign θ belongs to {−1,0,1}. "
                + "When θ ≠ 0 the zero parameter satisfies ½ ≤ β ≤ 1. When θ = 1 it also satisfies "
                + "s/(Q² log Q) ≤ 1 − β. The choice of β has no effect for θ = 0.")),
            Describe.Lean(DescribeId.Create("dyadic-endpoints"),
                DeclarationHandle.Create("D5/S3/CharacterSums/DyadicPrimeClassCount.dyadic_class_count"),
                H("Two endpoint estimates give a lower bound for the interval"),
                StatementSource.FromAuthor(EndpointClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For θ = 1 set W = 1 − Y^(β−1), and otherwise set W = 1. "
                    + "The derivative (1 − θ t^(β−1))/log t gives an increment of at least WY/log(2Y). "
                    + "Integration also gives F(Y) + F(2Y) ≤ 24 WY/log Y. Subtracting the endpoint estimates "
                    + "cancels the common offset e. Nonnegativity of the count allows truncation at zero. "
                    + "The exceptional-zero distance gives W ≥ min(1,s)/(2Q²)."))), DescribeRole.Theorem),
            Paragraph(Text("Write E(P;B,A,c,s) for the cyclotomic estimate. For each m ≥ 3 and each a coprime "
                + "to m there exist 1 < Q ≤ m, θ, β and a real offset e satisfying S(θ,β,Q,s). "
                + "For every t ≥ Qᴮ the absolute difference between φ(m)(P(m,a;0,t) + e) and F(t) "
                + "is at most A(exp(−c log t/log Q) + exp(−√(c log t))) F(t). The witnesses, "
                + "including e, stay fixed as t varies.")),
            Describe.Lean(DescribeId.Create("uniform-dyadic-count"),
                DeclarationHandle.Create("D5/S3/CharacterSums/DyadicPrimeClassCount.uniform_dyadic_class_count"),
                H("One pair of thresholds works for all reduced residue classes"),
                StatementSource.FromAuthor(UniformClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take u = 2A/ε, k = max(1,B,u/c), K = k + 1, and "
                        + "D₀ = 2 max(16,exp(u²/c)). At both D/2 and D, each exponential multiplied "
                        + "by A is at most ε/2. Apply the endpoint theorem with Q ≤ m.")),
                    Paragraph(Text("For ε = 1/100 and Y = D/2 ≥ 16, use log(2Y) ≤ 2 log Y. "
                        + "Then M(ε,Y) ≥ (13/50)Y/log Y. Since φ(m) ≤ m, the count is at least "
                        + "(13/100) min(1,s) Y/(m³ log Y).")),
                    Paragraph(Text("Thorner and Zaman, A unified and improved Chebotarev density theorem, "
                        + "Algebra & Number Theory 13 (2019), DOI 10.2140/ant.2019.13.1039, "
                        + "Theorem 1.4 (p. 1042) gives the relative asymptotic in writing, and Theorem 3.3 "
                        + "(p. 1052) gives the exceptional-zero distance. Take L = ℚ(ζₘ), H = Gal(L/ℚ) "
                        + "and fixed field ℚ. The character conductors divide m. For p coprime to m, "
                        + "Frobenius raises roots of unity to the pth power. The Lean theorem takes "
                        + "the resulting cyclotomic estimate E as a hypothesis."))), DescribeRole.Theorem))));

    private static Formula EndpointClaim()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var y = F.Id("Y");
        var q = F.Id("Q");
        var s = F.Id("s");
        var e = F.Id("e");
        var t = F.Id("t");
        var twoY = F.Seq(Num(2), y);
        return Aligned(
            F.Seq(Quant(F.Forall, "N", m, a), Quant(F.Forall, "Z", F.Theta),
                Quant(F.Forall, "R", F.Beta, y, q, s, e, F.Varepsilon)),
            F.Seq(y, F.Ge, F.Sp, Num(16), F.Land, F.Sp, q, F.Gt, Num(1), F.Land, F.Sp, s, F.Gt, Num(0),
                F.Land, F.Sp, F.Varepsilon, F.Ge, F.Sp, Num(0), F.Land, F.Sp, At("S", F.Theta, F.Beta, q, s)),
            F.Seq(F.Land, F.Sp, F.Open, F.Theta, F.Eq, Num(1), F.Implies, F.Sp, q, F.Le, F.Sp, y, F.Close),
            F.Seq(F.Land, F.Sp, F.Open, F.Forall, F.Sp, t, F.InMacro, F.Sp, F.OpenBrace, y, F.Comma, twoY, F.CloseBrace,
                F.Comma, F.Thin, F.Lvert, Phi(m), F.Open, At("P", m, a, Num(0), t), F.Plus, e, F.Close,
                F.Minus, At("F", t), F.Rvert, F.Le, F.Sp, F.Varepsilon, F.Sp, At("F", t), F.Close),
            F.Seq(F.Implies, F.Sp, Bound(m, a, s, q, y, twoY)));
    }

    private static Formula UniformClaim()
    {
        var b = F.Id("B");
        var aBound = F.Id("A");
        var c = F.Id("c");
        var s = F.Id("s");
        var k = F.Id("K");
        var d = F.Id("D");
        var threshold = F.Seq(d, F.Underscore, F.Grp(Num(0)));
        var m = F.Id("m");
        var a = F.Id("a");
        return Aligned(
            F.Seq(Quant(F.Forall, "R", b, aBound, c, s, F.Varepsilon), aBound, F.Gt, Num(0), F.Land, F.Sp,
                c, F.Gt, Num(0), F.Land, F.Sp, s, F.Gt, Num(0), F.Land, F.Sp, F.Varepsilon, F.Gt, Num(0), F.Land, F.Sp,
                At("E", F.Id("P"), b, aBound, c, s)),
            F.Seq(F.Implies, F.Sp, Quant(F.Exists, "R", k, threshold), k, F.Gt, Num(0), F.Land, F.Sp, threshold,
                F.Gt, Num(0), F.Land, F.Sp, F.OpenBracket, Quant(F.Forall, "N", m, a), Quant(F.Forall, "R", d)),
            F.Seq(m, F.Ge, F.Sp, Num(3), F.Land, F.Sp, At("gcd", a, m), F.Eq, Num(1), F.Land, F.Sp, d, F.Ge, F.Sp,
                At("max", threshold, F.Seq(F.Open, Num(4), m, F.Close, F.Caret, F.Grp(k)))),
            F.Seq(F.Implies, F.Sp, Bound(m, a, s, m, F.Seq(d, F.Slash, Num(2)), d), F.CloseBracket));
    }

    private static Formula Bound(Formula m, Formula a, Formula s, Formula q, Formula lo, Formula hi) =>
        F.Seq(F.Frac, F.Grp(At("min", Num(1), s)), F.Grp(Num(2), q, F.Caret, F.Grp(Num(2))),
            At("M", F.Varepsilon, lo), F.Le, F.Sp, Phi(m), At("P", m, a, lo, hi));

    private static Formula Phi(Formula m) => F.Seq(F.Varphi, F.Open, m, F.Close);

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Quant(Formula quantifier, string domain, params Formula[] variables) =>
        F.Seq(quantifier, F.Sp, F.Seq([.. variables.SelectMany((v, i) => i == 0 ? new[] { v } : [F.Comma, v])]),
            F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id(domain)), F.Comma, F.Thin);

    private static Formula Aligned(params Formula[] lines) =>
        F.Disp(F.Seq(F.Begin, F.Grp(F.Id("aligned")),
            F.Seq([.. lines.SelectMany((line, i) => i == 0 ? new[] { F.Amp, line } : [F.RowBreak, F.Amp, line])]),
            F.End, F.Grp(F.Id("aligned"))));
}
