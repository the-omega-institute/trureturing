using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.BlindPrimes;

internal sealed class IntegerPairClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/BlindPrimes/IntegerPairClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer residues agree exactly at prime divisors of the difference; for distinct "
            + "integers the blind prime set is finite and the separating set is cofinite.",
        H("Exact Blind-Prime Classification for Integer Pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residue-equality-is-divisibility-of-the-difference"),
                DeclarationHandle.Create(Prefix + "prime_residue_eq_iff_dvd_difference"),
                H("Residue equality is divisibility of the difference"),
                StatementSource.FromAuthor(CoreFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Integer modular equality is Mathlib's integer congruence relation. "
                        + "Its divisibility characterization gives the ordered difference "
                        + "after negating the opposite subtraction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("blind-primes-are-exactly-prime-divisors"),
                DeclarationHandle.Create(Prefix + "blind_primes_eq_primeDivisors"),
                H("Blind primes are exactly prime divisors"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Extensionality applies the residue-divisibility equivalence at each "
                        + "prime index. No distinctness hypothesis is needed for this exact "
                        + "set identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-integers-have-finitely-many-blind-primes"),
                DeclarationHandle.Create(Prefix + "blind_primes_finite"),
                H("Distinct integers have finitely many blind primes"),
                StatementSource.FromAuthor(FinitenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero difference has nonzero absolute value. Every blind prime "
                        + "therefore lies over the finite divisor finset of that absolute "
                        + "value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-separating-prime-set-is-cofinite"),
                DeclarationHandle.Create(Prefix + "separating_primes_compl_finite"),
                H("The separating prime set is cofinite"),
                StatementSource.FromAuthor(CofinitenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Within the prime-index subtype, the complement of the separating set "
                        + "is the blind set. Its finiteness proves cofiniteness. Natural and "
                        + "Dirichlet density are not claimed because pinned Mathlib has no "
                        + "usable definitions for them."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinctness-is-required-for-blind-set-finiteness"),
                DeclarationHandle.Create(
                    Prefix + "distinctness_is_necessary_for_blind_primes_finite"),
                H("Distinctness is required for blind-set finiteness"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the concrete equal pair zero and zero, every prime is blind. The "
                        + "prime subtype is infinite, so this blind set is not finite."))),
                DescribeRole.Theorem))));

    private static Formula CoreFormula()
    {
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, p, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            x, Comma, Sp, y, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
            Call("primeResidue", p, x), Sp, Eq, Sp, Call("primeResidue", p, y),
            Sp, Iff, Sp, p, Sp, Mid, Sp, Subtract(x, y), Dot));
    }

    private static Formula ClassificationFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")),
            Comma, Sp, Call("blindPrimes", x, y), Sp, Eq, Sp,
            Call("primeDivisors", Subtract(x, y)), Dot));
    }

    private static Formula FinitenessFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")),
            Comma, Sp, x, Sp, Neq, Sp, y, Sp, Rightarrow, Sp,
            Call("Finite", Call("blindPrimes", x, y)), Dot));
    }

    private static Formula CofinitenessFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")),
            Comma, Sp, x, Sp, Neq, Sp, y, Sp, Rightarrow, Sp,
            Call("Finite", Call("compl", Call("separatingPrimes", x, y))), Dot));
    }

    private static Formula NecessityFormula() =>
        Disp(Seq(
            Neg, Call("Finite", Call("blindPrimes", D(0), D(0))), Dot));
}
