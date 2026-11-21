using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DyadicPrimeClassCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic prime counts from two relative Chebotarev estimates",
        H("Effective prime counts in a varying residue class"),
        Blocks(
            Paragraph(Text("Write P(m,a;l,u) for the number of primes congruent to a modulo m "
                + "in the half-open interval (l,u]. Let Li(t) be the integral of 1/log u from 2 to t. "
                + "The main term is F(t) = Li(t) − θ Li(tᵝ), where θ is −1, 0 or 1. "
                + "Here ½ ≤ β < 1. When θ = 0 the choice of β has no effect.")),
            Describe.Lean(DescribeId.Create("dyadic-endpoints"),
                DeclarationHandle.Create("D5/S3/CharacterSums/DyadicPrimeClassCount.dyadic_class_count"),
                H("Two endpoint estimates give a lower bound for the interval"),
                StatementSource.FromAuthor(Bound(F.Id("Q"))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let Y ≥ 16, 1 < Q ≤ Y and s > 0. At t = Y and 2Y, suppose "
                        + "φ(m)(P(m,a;0,t) + e) differs from F(t) by at most F(t)/100, "
                        + "with the same offset e at both endpoints. When θ = 1, assume "
                        + "1 − β ≥ s/(Q² log Q). Then the displayed bound holds.")),
                    Paragraph(Text("For θ = 1 put W = 1 − Y^(β−1), and otherwise put W = 1. "
                        + "The derivative (1 − θ t^(β−1))/log t gives an increment of at least "
                        + "WY/(2 log Y). Bounding the logarithmic integrals gives "
                        + "F(Y) + F(2Y) ≤ 24 WY/log Y. Subtracting the two estimates cancels e "
                        + "and retains at least WY/(4 log Y). The exceptional-zero distance gives "
                        + "W ≥ min(1,s)/(2Q²)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-dyadic-count"),
                DeclarationHandle.Create("D5/S3/CharacterSums/DyadicPrimeClassCount.uniform_dyadic_class_count"),
                H("One pair of thresholds works for all reduced residue classes"),
                StatementSource.FromAuthor(Bound(F.Id("m"))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the cyclotomic relative prime-count estimate with exponent B, "
                        + "absolute constants A,c,s > 0, and a conductor bound 1 < Q ≤ m. "
                        + "For t ≥ Qᴮ its relative error is bounded by "
                        + "A(exp(−c log t/log Q) + exp(−√(c log t))). Then some K,D₀ > 0 "
                        + "work for every m ≥ 3, every reduced class a and every "
                        + "D ≥ max(D₀,(4m)ᴷ), with Y = D/2. Since φ(m) ≤ m this gives "
                        + "at least min(1,s) Y/(8m³ log Y) primes.")),
                    Paragraph(Text("Take k = max(1,B,200A/c), K = k + 1, and "
                        + "D₀ = 2 max(16,exp((200A)²/c)). At either endpoint the two exponentials, "
                        + "each multiplied by A, are at most 1/200. The endpoint theorem now applies.")),
                    Paragraph(Text("Thorner and Zaman, A unified and improved Chebotarev density theorem, "
                        + "Algebra & Number Theory 13 (2019), DOI 10.2140/ant.2019.13.1039, "
                        + "Theorem 1.4 (p. 1042) supplies the relative asymptotic in writing, "
                        + "and Theorem 3.3 (p. 1052) supplies the exceptional-zero distance. "
                        + "For the cyclotomic field of conductor dividing m, take H to be the full "
                        + "Galois group, whose fixed field is the rationals. The character conductors "
                        + "divide m. Above m, Frobenius acts by raising roots of unity to the pth "
                        + "power. The Lean theorem assumes the resulting analytic estimate explicitly."))),
                DescribeRole.Theorem))));

    private static Formula Bound(Formula q)
    {
        var y = F.Id("Y");
        var min = new Formula.FunctionCall(FormulaIdentifier.Create("min"), [Num(1), F.Id("s")]);
        var denominator = F.Seq(Num(8), F.Sp, q, F.Caret, F.Grp(Num(2)), F.Sp, F.Log, F.Sp, y);
        var lower = F.Seq(F.Frac, F.Grp(min, F.Sp, y), F.Grp(denominator));
        var phi = F.Seq(F.Phi, F.Open, F.Id("m"), F.Close);
        var primes = new Formula.FunctionCall(FormulaIdentifier.Create("P"),
            [F.Id("m"), F.Id("a"), y, F.Seq(Num(2), F.Sp, y)]);
        return F.Disp(new Formula.Relation(lower, FormulaRelationOperator.LessThanOrEqual,
            F.Seq(phi, F.Sp, primes)));
    }
}
