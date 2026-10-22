using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class DivisorCountRadicalCoincidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive integer whose divisor count divides its squarefree kernel has those two quantities equal.",
        H("Divisor Count and Radical Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-factors-bound-for-divisor-count"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/DivisorCountRadicalCoincidence.primeFactors_card_le_cardFactors_card_divisors"),
                H("Distinct prime factors bound the prime factors of the divisor count"),
                StatementSource.FromAuthor(PrimeFactorsBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonzero natural number k, the number of its distinct prime factors "
                        + "is at most the number of prime factors of its divisor count, counted "
                        + "with multiplicity. Each positive exponent contributes a factor "
                        + "greater than one to the prime-exponent product for the divisor count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("divisor-count-equals-radical-under-divisibility"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/DivisorCountRadicalCoincidence.radical_eq_card_divisors_of_dvd"),
                H("Divisibility forces equality"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The radical is squarefree, so every divisor of it is squarefree. "
                            + "The prime-exponent product for the divisor count contributes "
                            + "at least one prime factor for every distinct prime factor of k. "
                            + "Divisibility gives the reverse bound on distinct prime factors. "
                            + "The two prime-factor sets therefore coincide, and their products "
                            + "give the stated equality."))),
                DescribeRole.Theorem))));

    private static Formula PrimeFactorsBoundFormula()
    {
        Formula k = F.Id("k");
        Formula divisorCount = Call("card", Call("divisors", k));
        Formula countFactors = Seq(
            Operatorname, Grp(F.Id("ArithmeticFunction")), Dot,
            Operatorname, Grp(F.Id("cardFactors")), Parenthesized(divisorCount));
        return Disp(Seq(
            Forall, Sp, k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            k, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Call("card", Call("primeFactors", k)), Sp, Le, Sp, countFactors));
    }

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("k");
        Formula divisorCount = Call("card", Call("divisors", k));
        Formula radical = Call("radical", k);

        return Disp(Seq(
            Forall, Sp, k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            D(1), Sp, Le, Sp, k, Sp, Rightarrow, Sp,
            divisorCount, Sp, Mid, Sp, radical, Sp, Rightarrow, Sp,
            radical, Sp, Eq, Sp, divisorCount));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
