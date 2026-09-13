using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A003161PrimeSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/A003161PrimeSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A003161 at odd indices satisfies a congruence modulo each odd prime square.",
        H("A003161 modulo prime squares"),
        Blocks(
            Paragraph(Text(
                "For each natural N, let a(N) be the sum of the cubes of the differences "
                    + "between choose(N,j) and choose(N,j-1), over j from zero through floor(N/2). "
                    + "The binomial coefficient with lower index minus one is zero. "
                    + "For positive n, set b(n)=a(2n-1).")),
            Describe.Lean(
                DescribeId.Create("shifted-binomial-prime-square"),
                DeclarationHandle.Create(Prefix + "choose_mul_sub_one_mod_prime_sq"),
                H("Shifted binomial coefficients"),
                StatementSource.FromAuthor(EndpointStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induct on the upper block index using Vandermonde's identity. "
                        + "Each interior coefficient from the prime row is divisible by the prime. "
                        + "Lucas's theorem gives a common factor times alternating signs for "
                        + "the other coefficients. The alternating binomial sum vanishes exactly, "
                        + "so the interior convolution vanishes modulo the prime square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a003161-prime-square"),
                DeclarationHandle.Create(Prefix + "a003161_prime_square"),
                H("The ballot-cube congruence"),
                StatementSource.FromAuthor(SequenceStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Split the sum into blocks of prime length. At interior positions, "
                            + "the sum of two adjacent binomial coefficients is divisible by "
                            + "the prime. The cube of their difference is therefore congruent "
                            + "to four times the difference of their cubes modulo the prime square. "
                            + "These differences telescope, and the shifted binomial congruence "
                            + "identifies the two endpoints. The remaining block boundaries "
                            + "are the terms of the smaller ballot-cube sum.")),
                    Paragraph(Text(
                        "The conclusion holds for every positive index, including indices "
                            + "divisible by the prime. The stronger modulus given by the prime cube "
                            + "and the supercongruence with modulus p^(3k) remain separate questions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Mul(Formula x, Formula y) => F.Seq(x, F.Cdot, y);
    private static Formula SubOne(Formula x) => F.Seq(x, F.Minus, F.D(1));
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Positive(Formula x) =>
        new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, x);
    private static Formula OddPrime(Formula p) =>
        And(Call("Prime", p), F.Seq(p, F.Neq, F.D(2)));
    private static Formula Congruent(Formula x, Formula y, Formula p) =>
        new Formula.Relation(new Formula.Modulo(x, F.Seq(p, F.Caret, F.Grp(F.D(2)))),
            FormulaRelationOperator.Equal,
            new Formula.Modulo(y, F.Seq(p, F.Caret, F.Grp(F.D(2)))));
    private static Formula ForNat(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable),
            F.Seq(F.Mathbb, F.Grp(F.Id("N"))), body);

    private static Formula EndpointStatement()
    {
        Formula m = F.Id("m"), a = F.Id("a"), p = F.Id("p");
        return F.Disp(ForNat("m", ForNat("a", ForNat("p",
            new Formula.Logic(And(Positive(m), OddPrime(p)), FormulaLogicOperator.Implies,
                Congruent(Call("choose", SubOne(Mul(m, p)), Mul(a, p)),
                    Call("choose", SubOne(m), a), p))))));
    }

    private static Formula SequenceStatement()
    {
        Formula n = F.Id("n"), p = F.Id("p");
        return F.Disp(ForNat("n", ForNat("p",
            new Formula.Logic(And(Positive(n), OddPrime(p)), FormulaLogicOperator.Implies,
                Congruent(Call("b", Mul(n, p)), Call("b", n), p)))));
    }
}
