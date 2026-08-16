using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class PrimeGenealogyCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The number of ordered prime-factor genealogies is the multinomial of the prime "
        + "multiplicities.",
        H("Ordered Prime-Factor Genealogies"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-genealogy-count-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Combinatorics/PrimeGenealogyCount."
                    + "prime_genealogy_count_formula"),
                H("Prime-factor orderings have the multinomial count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("c"), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    Frac,
                    Grp(Open, Sum, Underscore, Grp(F.Id("p")), Sp,
                        F.Id("a"), Underscore, Grp(F.Id("p")), Close, Bang),
                    Grp(Prod, Underscore, Grp(F.Id("p")), Sp,
                        F.Id("a"), Underscore, Grp(F.Id("p")), Bang)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a natural number n, let a_p be the exponent of p in the canonical "
                        + "prime factorization of n. An ordered prime-factor genealogy is a distinct "
                        + "ordering of that prime-factor multiset. Its count is the factorial of the "
                        + "total multiplicity, sum_p a_p, divided by the product of the individual "
                        + "factorials, product_p a_p!. The formula also covers zero and one under "
                        + "Mathlib's canonical prime-factor-list convention.")),
                    Paragraph(Text(
                        "The Lean proof does not reconstruct the permutation count. Pinned Mathlib "
                        + "already defines Multiset.countPerms through Finsupp.multinomial and proves "
                        + "that the factorization of n is the frequency table of its canonical prime "
                        + "factor list. The deposited theorem only rewrites those two upstream truths "
                        + "into the factorial quotient at this repository address.")),
                    Paragraph(Text(
                        "This closes only the explicit multinomial count formula in the source atom. "
                        + "The recurrence over prime divisors, the maximal-chain interpretation, the "
                        + "prime-zeta generating series, its growth exponent, and the numerical "
                        + "asymptotic constant remain outside this claim."))),
                DescribeRole.Theorem
            ))));
}
