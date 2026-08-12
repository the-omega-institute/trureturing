using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class FreeCommMonoidDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive naturals under multiplication form the free commutative monoid on the primes.",
        H("The Free Commutative Monoid on the Prime Axes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pnat-free-comm-monoid"),
                DeclarationHandle.Create("D5/S3/Factorization/FreeCommMonoid.pnat_free_comm_monoid_on_primes"),
                H("Prime factorization is an isomorphism onto the free monoid on the primes"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("m"), Comma, F.Id("n"), InMacro, Sp,
                                    Mathbb, Grp(F.Id("N")), Underscore, Grp(Plus), Comma, Esc,
                                    Operatorname, Grp(F.Id("v")), Underscore, Grp(F.Id("p")),
                                    Open, F.Id("m"), F.Id("n"), Close,
                                    Eq,
                                    Operatorname, Grp(F.Id("v")), Underscore, Grp(F.Id("p")),
                                    Open, F.Id("m"), Close,
                                    Plus,
                                    Operatorname, Grp(F.Id("v")), Underscore, Grp(F.Id("p")),
                                    Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The deposited statement packages the freeness reading of unique "
                                        + "factorization in four clauses. First, the prime-factorization map "
                                        + "from the positive naturals under multiplication to the multiset "
                                        + "monoid over the primes, written multiplicatively, is bijective. "
                                        + "Second, it is multiplicative, so it is a monoid isomorphism. "
                                        + "Third, the target has the universal property of the free "
                                        + "commutative monoid on the primes: every prime-indexed family in "
                                        + "any commutative monoid extends to a unique monoid homomorphism "
                                        + "out of the multiset monoid. Fourth, the prime-exponent readouts "
                                        + "are additive: on each prime axis the exponent of a product is the "
                                        + "sum of the exponents of the factors, with no nonzeroness side "
                                        + "condition because positive naturals never vanish.")),
                                    Paragraph(Text(
                                        "The isomorphism clauses are a thin honest upgrade of pinned "
                                        + "mathlib: the underlying equivalence is the prime multiset "
                                        + "equivalence, its multiplicativity is the factor-multiset product "
                                        + "law, and the exponent additivity is the factorization product "
                                        + "law read on positive naturals. The universal-property clause is "
                                        + "proved natively: the extension maps a multiset of primes through "
                                        + "the family and takes the product, and uniqueness is multiset "
                                        + "induction against the two homomorphism laws. Pinned mathlib has "
                                        + "no named free-commutative-monoid universal-property interface, "
                                        + "so that clause is new glue rather than a citation.")),
                                    Paragraph(Text(
                                        "This is the freeness half of the prime-axis coordinate reading: "
                                        + "multiplication of positive naturals is coordinatewise addition "
                                        + "of prime exponents, so the primes are free axes and no relation "
                                        + "ever couples two axes. No claim is made here about unique "
                                        + "factorization in general monoids, about the golden or Zeckendorf "
                                        + "digit encodings of the exponents, or about any ordering or "
                                        + "density structure on the primes."))),
                DescribeRole.Theorem
            ))));
}
