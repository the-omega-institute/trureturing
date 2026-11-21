using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class MovingPrimeRowWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Keeping one auxiliary prime pair throughout a power window",
        H("The sharp window width"),
        Blocks(
            Paragraph(Text("Fix a prime q congruent to 3 modulo 8, write L = log q, and suppose L > 1. "
                + "For b > 1, call W(q,b) the following property. For every real threshold R and every "
                + "positive tolerance η there exist Y ≥ max(R,exp(5)), a loss 0 < ε < min(η,1/52), "
                + "and a single prime d congruent to 7 modulo 16, valid at every real x in [Y,Yᵇ].")),
            Paragraph(Text("Write u = x^(ε/5). The bands are u/2 < log q ≤ u and "
                + "u(log x)²/2 < log d ≤ u(log x)². The Jacobi symbols at q and at every odd "
                + "prime p ≤ u equal 1 for numerator −d, and −d is 1 modulo 8. "
                + "For every integer n from 1 to 2x^(2+8ε), log(4nqd) ≤ 2u(log x)².")),
            Describe.Lean(DescribeId.Create("prime-row-width"),
                DeclarationHandle.Create("D5/S3/Arith/MovingPrimeRowWidth.prime_pair_power_window_iff"),
                H("A strict width criterion"), StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compare the lower bound for log d at Yᵇ with the upper bound at Y. "
                        + "After cancellation, b² u(Y)^(b−1) < 2. Since L ≤ u(Y), equality at the "
                        + "claimed threshold already rules out a witness.")),
                    Paragraph(Text("Conversely choose d arbitrarily large, split at q and all odd primes "
                        + "up to the ceiling of Lᵇ. Set a = √(log(d)/L), Y = exp(a), and ε = 5 log(L)/a. "
                        + "At x = exp(sa) with 1 ≤ s ≤ b, u = Lˢ and u(log x)²/log d = s² L^(s−1). "
                        + "This ratio lies in [1,2), and both prime size bands follow. Increasing d "
                        + "makes Y arbitrarily large and ε arbitrarily small. For log x ≥ 5 the spare "
                        + "u(log x)² in the conductor bound covers log(4nq).")),
                    Paragraph(Text("This criterion proves the arithmetic row. The simultaneous character "
                        + "estimates and zero exclusions for the same pair, and comparison thresholds for "
                        + "a varying loss, remain separate analytic inputs."))), DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var q = F.Id("q");
        var b = F.Id("b");
        var l = At("log", q);
        var prime = At("Prime", q);
        var residue = new Formula.Relation(At("mod", q, F.D(8)), FormulaRelationOperator.Equal, F.D(3));
        var admissible = And(prime, And(residue, Less(F.D(1), l)));
        var width = Less(F.Seq(Power(b, F.D(2)), Power(l, F.Seq(b, F.Minus, F.D(1)))), F.D(2));
        var equivalence = new Formula.Logic(At("W", q, b), FormulaLogicOperator.Iff, width);
        return F.Disp(All("q", "N", Implies(admissible, All("b", "R", Implies(Less(F.D(1), b), equivalence)))));
    }

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, string domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            F.Seq(F.Mathbb, F.Grp(F.Id(domain))), body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Power(Formula a, Formula b) => F.Seq(a, F.Caret, F.Grp(b));
}
