using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.ExponentCoordinates;

internal sealed class PrimeExponentBijectionDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive naturals are exactly the finite prime-supported exponent families.",
        H("Prime-Exponent Bijection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-exponent-product"),
                DeclarationHandle.Create(Root + "primeExponentProduct"),
                H("Finite prime-power product"),
                StatementSource.FromAuthor(ProductDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A prime-supported exponent family reconstructs a positive natural by the "
                        + "finite product of each prime raised to its stored exponent."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("prime-exponent-language-equivalence"),
                DeclarationHandle.Create(Root + "primeExponentLanguageEquiv"),
                H("Prime-exponent language equivalence"),
                StatementSource.FromAuthor(EquivalenceDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equivalence is Mathlib's factorization equivalence, with the existing "
                        + "repository prime-exponent language as its forward value."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("prime-exponent-language-equivalence-uses-existing-map"),
                DeclarationHandle.Create(Root + "prime_exponent_language_equiv_apply"),
                H("The equivalence uses the existing prime-exponent language"),
                StatementSource.FromAuthor(ForwardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive natural, the forward value of the equivalence is exactly "
                        + "the previously defined primeExponentLanguage readout."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("prime-exponent-product-is-the-prime-power-product"),
                DeclarationHandle.Create(Root + "prime_exponent_product_formula"),
                H("The inverse is the finite product of prime powers"),
                StatementSource.FromAuthor(ProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The underlying natural of the named inverse is the finite Finsupp product "
                        + "of p to the exponent e(p)."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("prime-exponent-language-is-bijective-on-prime-support"),
                DeclarationHandle.Create(Root + "prime_exponent_language_bijection"),
                H("Prime-exponent language is bijective on prime support"),
                StatementSource.FromAuthor(BijectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Injectivity is reused from prime_exponent_language_complete. Surjectivity "
                        + "comes directly from Nat.factorizationEquiv; no factorization theorem "
                        + "is reproved."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("positivity-restriction-is-necessary"),
                DeclarationHandle.Create(Root + "positivity_restriction_is_necessary"),
                H("Positivity is necessary"),
                StatementSource.FromAuthor(PositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On all naturals, zero and one both have the empty factorization, so the raw "
                        + "factorization function is not injective."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("prime-support-restriction-is-necessary"),
                DeclarationHandle.Create(Root + "prime_support_restriction_is_necessary"),
                H("Prime support is necessary"),
                StatementSource.FromAuthor(PrimeSupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unrestricted Finsupp codomain contains a family with exponent one at "
                        + "the composite four. Every natural factorization is zero there, so that "
                        + "family has no preimage. PrimeExponentTable excludes it by type."))),
                DescribeRole.Theorem
            ))));

    private static Formula ProductDefinition() => Disp(Seq(
        F.Id("primeExponentProduct"), Colon, Sp, F.Id("PrimeExponentTable"),
        Sp, Rightarrow, Sp, Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0))));

    private static Formula EquivalenceDefinition() => Disp(Seq(
        F.Id("primeExponentLanguageEquiv"), Colon, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)),
        Sp, Sim, Sp, F.Id("PrimeExponentTable")));

    private static Formula ForwardFormula() => Disp(Seq(
        Forall, Sp, F.Id("n"), Comma, Sp,
        Call("primeExponentLanguageEquiv", F.Id("n")), Sp, Eq, Sp,
        Call("primeExponentLanguage", F.Id("n"))));

    private static Formula ProductFormula() => Disp(Seq(
        Forall, Sp, F.Id("e"), Comma, Sp,
        Call("primeExponentProduct", F.Id("e")), Sp, Eq, Sp,
        Prod, Underscore, Grp(F.Id("p")), Sp,
        F.Id("p"), Caret, Grp(Call("e", F.Id("p")))));

    private static Formula BijectionFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("Bijective")),
        Open, F.Id("primeExponentLanguageEquiv"), Close));

    private static Formula PositivityFormula() => Disp(Seq(
        Neg, Operatorname, Grp(F.Id("Injective")),
        Open, F.Id("factorization"), Colon, Mathbb, Grp(F.Id("N")),
        Sp, Rightarrow, Sp, F.Id("Finsupp"), Close));

    private static Formula PrimeSupportFormula() => Disp(Seq(
        Neg, Operatorname, Grp(F.Id("Surjective")),
        Open, F.Id("primeExponentLanguage"), Colon,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)),
        Sp, Rightarrow, Sp, F.Id("Finsupp"), Close));
}
