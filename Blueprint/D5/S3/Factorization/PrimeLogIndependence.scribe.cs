using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class PrimeLogIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Factorization/PrimeLogIndependence",
            "The logarithms of the primes are linearly independent over the integers."),
        H("Integer Linear Independence of Prime Logarithms"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("prime-logarithms-are-integer-linearly-independent"),
                H("Prime logarithms are integer-linearly independent"),
                LeanTheorem(
                    "D5/S3/Factorization/PrimeLogIndependence.prime_log_indep"),
                Disp(Seq(
                    Forall, Sp, F.Id("S"), Comma, F.Id("k"), Comma, Sp,
                    Open, Forall, Sp, F.Id("p"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Close, Sp,
                    Rightarrow, RowBreak,
                    Sum, Underscore, Grp(F.Id("p"), Sp, InMacro, Sp, F.Id("S")), Sp,
                    F.Id("k"), Open, F.Id("p"), Close, Sp, Log, Sp, F.Id("p"), Eq, D(0), Sp,
                    Rightarrow, RowBreak,
                    Forall, Sp, F.Id("p"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
                    F.Id("k"), Open, F.Id("p"), Close, Eq, D(0))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For a finite set S of prime numbers and integer coefficients k, if the weighted "
                        + "sum of the logarithms log p over S vanishes, then every coefficient k p is "
                        + "zero. Equivalently, the logarithms of distinct primes are linearly independent "
                        + "over the integers, hence over the rationals.")),
                    Paragraph(Text(
                        "The proof splits S into the primes with nonnegative coefficient and those with "
                        + "negative coefficient. Exponentiating the vanishing sum turns it into an "
                        + "equality of two prime-power products, one over each part; these are products "
                        + "over disjoint sets of primes, so reading the prime-power factorization at any "
                        + "prime in either part forces that exponent, and therefore that coefficient, to "
                        + "vanish. The decisive step is the uniqueness of prime factorization.")),
                    Paragraph(Text(
                        "This is not a restatement of a library lemma: a search of Mathlib finds the "
                        + "prime-factorization multiplication and power laws and the exponential of a sum, "
                        + "but no linear independence of prime logarithms. The statement is the "
                        + "arithmetic core behind the dense winding of the zeta phase line on the torus of "
                        + "per-axis phases; only that independence is claimed here, not the topological "
                        + "density it implies.")))))));
}
