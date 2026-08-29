using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class ThreeRingProfileFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime three-ring profile factors uniquely through units modulo sixty.",
        H("Three-Ring Profile Factorisation Modulo Sixty"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-three-ring-profile"),
                DeclarationHandle.Create(DeclarationPrefix + "primeThreeRingProfile"),
                H("The splitting profile of a prime coprime to sixty"),
                StatementSource.FromAuthor(ProfileFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime unramified at two, three, and five, the three-ring "
                        + "profile is the canonical unit-class image evaluated at the "
                        + "prime's residue modulo sixty. The already-factored map on "
                        + "units is reused rather than redefined."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-factors-through-residue"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_three_ring_profile_factors_mod_sixty"),
                H("The profile depends only on the residue modulo sixty"),
                StatementSource.FromAuthor(FactorEquationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two primes with the same residue modulo sixty carry the same "
                        + "three-ring splitting profile, so the profile factors through "
                        + "the unit group of the integers modulo sixty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("factorisation-is-unique"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_three_ring_profile_factor_unique"),
                H("The factoring map is unique"),
                StatementSource.FromAuthor(UniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Exactly one map on units modulo sixty factors the three-ring "
                        + "profile of every prime coprime to sixty.")),
                    Paragraph(Text(
                        "Uniqueness needs each unit class to contain a prime, which "
                        + "Dirichlet's theorem on primes in arithmetic progressions "
                        + "supplies from pinned mathlib."))),
                DescribeRole.Theorem))));

    private static Formula Profile(Formula argument) =>
        new Formula.Apply(new Formula.Subscript(Sigma, Seq(D(3))), [argument]);

    private static Formula BarProfile(Formula argument) =>
        new Formula.Apply(F.Id("g"), [argument]);

    private static Formula ResidueOf(Formula prime) =>
        new Formula.Modulo(prime, D(6, 0));

    private static Formula ProfileFormula()
    {
        Formula prime = F.Id("p");
        return Disp(new Formula.Relation(
            Profile(prime),
            FormulaRelationOperator.Equal,
            BarProfile(ResidueOf(prime))));
    }

    private static Formula FactorEquationFormula()
    {
        Formula prime = F.Id("p");
        return Disp(Seq(
            Forall, Sp, prime, Comma, Sp,
            new Formula.Relation(
                Profile(prime),
                FormulaRelationOperator.Equal,
                BarProfile(ResidueOf(prime)))));
    }

    private static Formula UniquenessFormula()
    {
        Formula prime = F.Id("p");
        Formula factor = F.Id("f");
        Formula body = Seq(
            Forall, Sp, prime, Comma, Sp,
            new Formula.Relation(
                Profile(prime),
                FormulaRelationOperator.Equal,
                new Formula.Apply(factor, [ResidueOf(prime)])));
        return Disp(Seq(Exists, Bang, Sp, factor, Comma, Sp, body));
    }
}
