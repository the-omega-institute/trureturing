using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class PositiveRationalGroupDocument : IScribeDocumentDefinition
{
    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed prime exponents give the additive presentation of positive rationals.",
        H("Positive Rationals from Signed Prime Exponents"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-exponent-equivalence"),
                DeclarationHandle.Create("D5/S3/Factorization/PositiveRationalGroup.primeExponentEquivPositiveRational"),
                H("Signed prime ledgers map to positive rationals"),
                StatementSource.FromAuthor(Disp(Seq(
                                    F.Id("primeExponentEquivPositiveRational"), Colon,
                                    Open, F.Id("Prime"), Sp, Rightarrow, Sp, F.Id("Int"), Close,
                                    Sp, Sim, Sp, F.Id("PositiveRational")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The equivalence sends a finitely supported integer-valued function "
                                    + "on the natural primes to a positive rational. Addition of exponent "
                                    + "ledgers corresponds to multiplication of positive rationals."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("signed-prime-ledger-equivalence-is-bijective"),
                DeclarationHandle.Create("D5/S3/Factorization/PositiveRationalGroup.signed_prime_ledger_equiv_positive_rationals"),
                H("The prime-exponent equivalence is bijective"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Operatorname, Grp(F.Id("Bijective")),
                                    Open, F.Id("primeExponentEquivPositiveRational"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Every finite signed prime ledger determines exactly one positive "
                                        + "rational, and every positive rational has exactly one such ledger. "
                                        + "The codomain is represented as the units of the nonnegative "
                                        + "rationals, so zero is excluded by construction.")),
                                    Paragraph(Text(
                                        "The library was searched before proving. No direct equivalence "
                                        + "between positive rationals and integer prime exponents was found. "
                                        + "The proof instead constructs both groups as localizations of the "
                                        + "natural prime ledger and applies "
                                        + "AddSubmonoid.LocalizationMap.addEquivOfLocalizations. The "
                                        + "localization laws use "
                                        + "AddSubmonoid.isLocalizationMap_of_addGroup; natural-number "
                                        + "factorization enters through PNat.factorMultisetEquiv, "
                                        + "PNat.factorMultiset_mul, and Multiset.toFinsupp. This is a new "
                                        + "localization wrapper assembled from pinned library components, "
                                        + "not a wrapper around the complete statement. The source atom "
                                        + "contains no numerical certificate."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("rational-log-length-is-additive"),
                DeclarationHandle.Create("D5/S3/Factorization/PositiveRationalGroup.rational_log_length_add"),
                H("Rational logarithmic length is additive"),
                StatementSource.FromAuthor(Disp(Seq(
                                    F.Id("rationalLogLength"), Open,
                                    F.Id("a"), Plus, F.Id("b"), Close, Eq,
                                    F.Id("rationalLogLength"), Open, F.Id("a"), Close, Plus,
                                    F.Id("rationalLogLength"), Open, F.Id("b"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Transporting the natural logarithm through the equivalence extends "
                                    + "prime-exponent length to signed ledgers. The homomorphism law turns "
                                    + "ledger addition into rational multiplication, and Real.log_mul turns "
                                    + "that product into addition. A separate checked witness shows that "
                                    + "this extension takes negative values, as required for ratios below "
                                    + "one."))),
                DescribeRole.Theorem
            ))));
}
