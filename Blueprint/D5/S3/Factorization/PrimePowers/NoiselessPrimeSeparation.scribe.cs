using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class NoiselessPrimeSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PrimePowers/NoiselessPrimeSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime congruence distinguishes exactly away from divisors of the difference.",
        H("Noiseless Prime Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nondividing-modulus-separates"),
                DeclarationHandle.Create(Prefix + "nondividing_modulus_separates"),
                H("Every nondividing modulus separates"),
                StatementSource.FromAuthor(NondividingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary integer inputs n and m and every natural modulus p, "
                        + "failure of p to divide n minus m forces the two inputs to be "
                        + "incongruent modulo p. Primality and p at least two are not used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dividing-modulus-does-not-separate"),
                DeclarationHandle.Create(Prefix + "dividing_modulus_does_not_separate"),
                H("Every dividing modulus fails to separate"),
                StatementSource.FromAuthor(DividingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The converse is exact: if p divides n minus m, then n and m are "
                        + "congruent modulo p. This direction also needs no primality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-integers-have-distinguishing-prime"),
                DeclarationHandle.Create(
                    Prefix + "distinct_integers_have_distinguishing_prime"),
                H("A prime distinguishes every distinct integer pair"),
                StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n not equal to m, Euclid's theorem supplies a prime larger than "
                        + "the absolute difference. Such a prime cannot divide the difference, "
                        + "so the pointwise criterion makes it a distinguishing coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("indistinguishing-primes-finite"),
                DeclarationHandle.Create(Prefix + "indistinguishing_primes_finite"),
                H("Only finitely many primes fail to distinguish"),
                StatementSource.FromAuthor(FinitenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When n and m differ, every indistinguishing prime belongs to the finite "
                        + "primeFactors finset of the nonzero absolute difference. Thus almost "
                        + "every prime coordinate separates the pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinctness-hypothesis-is-necessary"),
                DeclarationHandle.Create(Prefix + "distinctness_hypothesis_is_necessary"),
                H("Distinctness is necessary"),
                StatementSource.FromAuthor(DistinctnessNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the concrete pair zero and zero no prime distinguishes the inputs, "
                        + "and every prime is indistinguishing. This simultaneously refutes "
                        + "existence and finiteness when distinctness is removed."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nondivisibility-hypothesis-is-necessary"),
                DeclarationHandle.Create(
                    Prefix + "nondivisibility_hypothesis_is_necessary"),
                H("Nondivisibility is necessary for separation"),
                StatementSource.FromAuthor(NondivisibilityNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two divides four minus zero, and four is congruent to zero modulo two. "
                        + "This concrete pair prevents deletion of the nondivisibility premise."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("divisibility-hypothesis-is-necessary"),
                DeclarationHandle.Create(Prefix + "divisibility_hypothesis_is_necessary"),
                H("Divisibility is necessary for nonseparation"),
                StatementSource.FromAuthor(DivisibilityNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two does not divide one minus zero, and one is not congruent to zero "
                        + "modulo two. This concrete pair prevents deletion of the divisibility "
                        + "premise from the converse."))),
                DescribeRole.Lemma))));

    private static Formula Difference(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, right);

    private static Formula DividesDifference(
        Formula modulus, Formula left, Formula right) =>
        Seq(modulus, Sp, Mid, Sp, Difference(left, right));

    private static Formula Prime(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Prime")), Open, value, Close);

    private static Formula ModEq(
        Formula modulus, Formula left, Formula right) =>
        Seq(Operatorname, Grp(F.Id("ModEq")), Open,
            modulus, Comma, Sp, left, Comma, Sp, right, Close);

    private static Formula PrimeModEqSet(Formula left, Formula right)
    {
        Formula prime = F.Id("p");
        return Seq(OpenBrace, prime, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp,
            Mid, Sp, Prime(prime), Sp, Land, Sp, ModEq(prime, left, right), CloseBrace);
    }

    private static Formula NondividingFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        return Disp(Seq(
            Forall, Sp, p, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            n, Comma, Sp, m, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, RowBreak,
            Neg, Open, DividesDifference(p, n, m), Close, Sp, Rightarrow, Sp,
            Neg, ModEq(p, n, m), Dot));
    }

    private static Formula DividingFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        return Disp(Seq(
            Forall, Sp, p, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            n, Comma, Sp, m, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, RowBreak,
            DividesDifference(p, n, m), Sp, Rightarrow, Sp, ModEq(p, n, m), Dot));
    }

    private static Formula ExistenceFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, m, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")),
            Comma, Sp, n, Sp, Neq, Sp, m, Sp, Rightarrow, RowBreak,
            Exists, Sp, p, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Prime(p), Sp, Land, Sp, Neg, ModEq(p, n, m), Dot));
    }

    private static Formula FinitenessFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, m, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")),
            Comma, Sp, n, Sp, Neq, Sp, m, Sp, Rightarrow, RowBreak,
            Operatorname, Grp(F.Id("Finite")), Open, PrimeModEqSet(n, m), Close, Dot));
    }

    private static Formula DistinctnessNecessityFormula()
    {
        Formula zero = D(0);
        Formula p = F.Id("p");
        Formula noWitness = Seq(
            Neg, Open, Exists, Sp, p, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, Prime(p), Sp, Land, Sp, Neg, ModEq(p, zero, zero), Close);
        Formula infinite = Seq(
            Operatorname, Grp(F.Id("Infinite")), Open,
            PrimeModEqSet(zero, zero), Close);
        return Disp(Seq(noWitness, Sp, Land, Sp, infinite, Dot));
    }

    private static Formula NondivisibilityNecessityFormula() =>
        Disp(Seq(
            DividesDifference(D(2), D(4), D(0)), Sp, Land, Sp,
            ModEq(D(2), D(4), D(0)), Dot));

    private static Formula DivisibilityNecessityFormula() =>
        Disp(Seq(
            Neg, Open, DividesDifference(D(2), D(1), D(0)), Close, Sp, Land, Sp,
            Neg, ModEq(D(2), D(1), D(0)), Dot));
}
