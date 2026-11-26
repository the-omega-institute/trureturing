using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class OeisA367865RadicalAverageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/OeisA367865RadicalAverage.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2026a367865");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The radical-weighted divisor sum is the radical average over a complete positive interval.",
        H("OEIS A367865 Radical Average"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("oeis-a367865-radical-average-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact identity for every positive n"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every positive natural n, the equality is interpreted in ℚ. "
                        + "The divisor sum uses positive Nat.divisors and the average uses Finset.Icc 1 n, "
                        + "so n = 1 remains in the statement.")),
                    Paragraph(Text("Set m = rad(n). The prime-factor product identity gives "
                        + "rad(nk) gcd(m,k) = m rad(k), hence the quotient is m/gcd(m,k). "
                        + "This function has period m. Grouping one period by gcd gives the "
                        + "totient-weighted divisor sum, and m divides n supplies complete periods.")),
                    Paragraph(Text("The squarefree radical m has exactly the squarefree divisors of n. "
                        + "Mathlib's Möbius square identity therefore turns the left side into the same "
                        + "totient-weighted divisor sum. The proof is the direct rational composition of "
                        + "these identities."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var k = F.Id("k");
        var divisors = Call(Qualified("Nat", "divisors"), n);
        var dsum = new Formula.Subscript(Sum, Seq(d, InMacro, divisors));
        var ksum = new Formula.Subscript(Sum,
            Seq(k, InMacro, Call(Qualified("Finset", "Icc"), D(1), n)));
        var rad = (Formula x) => Call("rad", x);
        var phi = (Formula x) => Seq(Phi, Par(x));
        var mu = (Formula x) => Seq(Mu, Par(x));
        var leftTerm = Mul(Mul(d, phi(d)), Pow(mu(d), D(2)));
        var rightTerm = Frac(rad(Mul(n, k)), rad(k));
        return Disp(Seq(
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Le, Sp, n, Sp, Rightarrow, Sp,
            Equal(Seq(dsum, Sp, leftTerm),
                Mul(Frac(rad(n), n), Seq(ksum, Sp, rightTerm)))));
    }

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string function, params Formula[] arguments) =>
        new Formula.Apply(F.Id(function), [.. arguments]);
    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula left, Formula right) =>
        new Formula.Power(left, right);
    private static Formula Frac(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
}
