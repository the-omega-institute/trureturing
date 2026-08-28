using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class RationalValuationRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Embeddings/RationalValuationRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime valuations form a direct-sum profile that recovers nonzero rationals.",
        H("Rational Recovery from Finite Valuations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-finite-valuation-profile"),
                DeclarationHandle.Create(Prefix + "rationalFiniteValuationProfile"),
                H("The finite-prime valuation profile"),
                StatementSource.FromAuthor(ProfileDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The profile assigns to a rational number the integer p-adic valuation at "
                        + "each natural prime p. Its finite support is contained in the union of "
                        + "the numerator and denominator factorization supports, so the codomain "
                        + "is the signed-prime direct sum rather than an unrestricted product."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-finite-valuation-profile-coordinate"),
                DeclarationHandle.Create(Prefix + "rationalFiniteValuationProfile_apply"),
                H("Profile coordinates are p-adic valuations"),
                StatementSource.FromAuthor(ProfileApplyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating the finitely supported profile at a prime returns exactly the "
                        + "Mathlib p-adic valuation at that prime. The finite-support packaging "
                        + "therefore does not alter any coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-profile-equality-iff-absolute-value-equality"),
                DeclarationHandle.Create(
                    Prefix + "rational_finite_valuation_profile_eq_iff_abs_eq"),
                H("Profiles classify nonzero rationals up to sign"),
                StatementSource.FromAuthor(ProfileIffAbsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonzero rationals, equality of every finite-prime valuation is "
                            + "equivalent to equality of absolute values. The forward direction "
                            + "cross-multiplies the reduced numerator and denominator data and "
                            + "uses injectivity of natural-number prime factorization.")),
                    Paragraph(Text(
                        "Primality is used for factorization coordinates and their uniqueness. "
                            + "No theorem about the distribution of primes is used, and merely "
                            + "assuming an index is greater than one would not identify a prime "
                            + "factorization coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-recovery-from-sign-and-valuations"),
                DeclarationHandle.Create(
                    Prefix + "rational_recovered_from_sign_and_finite_valuations"),
                H("Sign and finite valuations recover a rational uniquely"),
                StatementSource.FromAuthor(SignedRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal profiles first identify absolute values. Equality of the nonzero "
                        + "archimedean signs then excludes the opposite-value branch, leaving "
                        + "equality of the original rationals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-finite-valuation-kernel"),
                DeclarationHandle.Create(Prefix + "rational_finite_valuation_kernel"),
                H("Finite valuations leave exactly a sign ambiguity"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If two nonzero rationals have equal p-adic valuations at every prime, then "
                        + "their absolute values agree. Consequently one rational equals either "
                        + "the other rational or its negative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonzero-hypotheses-are-necessary"),
                DeclarationHandle.Create(Prefix + "nonzero_hypotheses_are_necessary"),
                H("Both nonzero hypotheses are necessary"),
                StatementSource.FromAuthor(NonzeroNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete pairs zero and one, in both orders, have identical finite "
                        + "valuations under Mathlib's totalized convention, but neither pair "
                        + "satisfies equality up to sign. Thus zero must be excluded on both "
                        + "sides."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sign-equality-is-necessary"),
                DeclarationHandle.Create(Prefix + "sign_equality_is_necessary"),
                H("The sign observation is necessary"),
                StatementSource.FromAuthor(SignNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One and minus one have the same finite-prime profile but are unequal. This "
                        + "concrete kernel pair proves that valuation data alone cannot select "
                        + "a sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("valuation-equality-is-necessary"),
                DeclarationHandle.Create(Prefix + "valuation_equality_is_necessary"),
                H("The valuation observation is necessary"),
                StatementSource.FromAuthor(ValuationNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive rationals one and two have equal signs but are unequal. This "
                        + "concrete pair proves that the sign readout cannot replace the finite "
                        + "valuation profile."))),
                DescribeRole.Theorem))));

    private static Formula ProfileDefinitionFormula()
    {
        Formula x = F.Id("x");
        Formula p = F.Id("p");
        return Disp(Seq(
            F.Id("nu"), Colon, Sp, RationalNumbers(), Sp, To, Sp,
            F.Id("SignedPrimeLedger"), Comma, Sp,
            ProfileCoordinate(x, p), Sp, Eq, Sp,
            Seq(F.Id("v"), Underscore, p, Open, x, Close), Dot));
    }

    private static Formula ProfileApplyFormula()
    {
        Formula x = F.Id("x");
        Formula p = F.Id("p");
        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, RationalNumbers(), Comma, Sp,
            p, Sp, InMacro, Sp, Seq(F.Id("Nat"), Dot, F.Id("Primes")), Comma, Sp,
            ProfileCoordinate(x, p), Sp, Eq, Sp,
            Seq(F.Id("v"), Underscore, p, Open, x, Close), Dot));
    }

    private static Formula ProfileIffAbsFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, RationalNumbers(), Comma, Sp,
            x, Sp, Neq, Sp, D(0), Sp, Land, Sp, y, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Open, Profile(x), Sp, Eq, Sp, Profile(y), Sp, Iff, Sp,
            Abs(x), Sp, Eq, Sp, Abs(y), Close, Dot));
    }

    private static Formula SignedRecoveryFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, RationalNumbers(), Comma, Sp,
            x, Sp, Neq, Sp, D(0), Sp, Land, Sp, y, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Profile(x), Sp, Eq, Sp, Profile(y), Sp, Land, Sp,
            Sign(x), Sp, Eq, Sp, Sign(y), Sp, Rightarrow, Sp,
            x, Sp, Eq, Sp, y, Dot));
    }

    private static Formula KernelFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula p = F.Id("p");
        Formula vpX = Seq(F.Id("v"), Underscore, p, Open, x, Close);
        Formula vpY = Seq(F.Id("v"), Underscore, p, Open, y, Close);
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, RationalNumbers(), Comma, Sp,
            x, Sp, Neq, Sp, D(0), Sp, Land, Sp, y, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Open, Forall, Sp, p, Comma, Sp, F.Id("Prime"), Open, p, Close,
            Sp, Rightarrow, Sp, vpX, Sp, Eq, Sp, vpY, Close, Sp, Rightarrow, Sp,
            Open, x, Sp, Eq, Sp, y, Sp, Lor, Sp, x, Sp, Eq, Sp, Minus, y, Close, Dot));
    }

    private static Formula NonzeroNecessaryFormula()
    {
        Formula zero = D(0);
        Formula one = D(1);
        Formula first = Seq(
            Profile(zero), Sp, Eq, Sp, Profile(one), Sp, Land, Sp,
            zero, Sp, Neq, Sp, one, Sp, Land, Sp, zero, Sp, Neq, Sp, Minus, one);
        Formula second = Seq(
            Profile(one), Sp, Eq, Sp, Profile(zero), Sp, Land, Sp,
            one, Sp, Neq, Sp, zero, Sp, Land, Sp, one, Sp, Neq, Sp, Minus, zero);
        return Disp(Seq(Open, first, Close, Sp, Land, Sp, Open, second, Close, Dot));
    }

    private static Formula SignNecessaryFormula() =>
        Disp(Seq(
            Profile(D(1)), Sp, Eq, Sp, Profile(Seq(Minus, D(1))), Sp, Land, Sp,
            D(1), Sp, Neq, Sp, Minus, D(1), Dot));

    private static Formula ValuationNecessaryFormula() =>
        Disp(Seq(
            Sign(D(1)), Sp, Eq, Sp, Sign(D(2)), Sp, Land, Sp,
            D(1), Sp, Neq, Sp, D(2), Dot));

    private static Formula Profile(Formula value) =>
        Seq(F.Id("nu"), Open, value, Close);

    private static Formula ProfileCoordinate(Formula value, Formula prime) =>
        Seq(Profile(value), Open, prime, Close);

    private static Formula Abs(Formula value) =>
        new Formula.Absolute(value);

    private static Formula Sign(Formula value) =>
        Seq(Operatorname, Grp(F.Id("sgn")), Open, value, Close);

    private static Formula RationalNumbers() =>
        Seq(Mathbb, Grp(F.Id("Q")));
}
