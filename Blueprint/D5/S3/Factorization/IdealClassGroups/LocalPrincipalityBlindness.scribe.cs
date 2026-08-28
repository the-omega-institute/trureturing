using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.IdealClassGroups;

internal sealed class LocalPrincipalityBlindnessDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dedekind prime-localization principality is constant and misses a concrete global gap.",
        H("Local Principality Is Blind to the Global Ideal Class"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fractional-ideal-localization"),
                DeclarationHandle.Create(Prefix + "localizedFractionalIdealAtPrime"),
                H("Extend a fractional ideal to a prime localization"),
                StatementSource.FromAuthor(LocalizedIdealFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named extension uses Mathlib's fractional-ideal extension homomorphism "
                        + "from the fraction field of the source domain to the fraction field of "
                        + "its localization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-principality-readout"),
                DeclarationHandle.Create(Prefix + "localPrincipalityReadout"),
                H("Read whether an ideal becomes principal at one prime"),
                StatementSource.FromAuthor(ReadoutDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This named predicate is the integral-ideal face of the local readout. It "
                        + "maps the ideal into the prime localization and asks whether it is "
                        + "principal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dedekind-localization-at-a-nonzero-prime-is-a-dvr"),
                DeclarationHandle.Create(Prefix + "localization_at_nonzero_prime_is_dvr"),
                H("A nonzero-prime localization of a Dedekind domain is a DVR"),
                StatementSource.FromAuthor(DvrFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof invokes Mathlib's exact Dedekind localization theorem. Primality "
                        + "forms the localization, while nonzeroness excludes the fraction-field "
                        + "case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("every-localized-fractional-ideal-is-principal"),
                DeclarationHandle.Create(
                    Prefix + "localized_fractional_ideal_is_principal"),
                H("Every fractional ideal in the localized DVR is principal"),
                StatementSource.FromAuthor(FractionalPrincipalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A DVR inherits Mathlib's principal-ideal-ring structure. The fractional "
                        + "ideal instance proves the result without a nonzero-ideal premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-local-principality-readout-is-always-true"),
                DeclarationHandle.Create(Prefix + "local_principality_readout_is_true"),
                H("Every Dedekind local-principality readout equals true"),
                StatementSource.FromAuthor(ReadoutTrueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mapped ideal lies in the same localized DVR, so its readout is true for "
                        + "every ideal, including zero and the unit ideal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nontrivial-class-group-forces-local-observer-blindness"),
                DeclarationHandle.Create(
                    Prefix
                        + "local_principality_observers_are_blind_of_nontrivial_class_group"),
                H("A nontrivial class group supplies an indistinguishable mixed pair"),
                StatementSource.FromAuthor(AbstractBlindWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Surjectivity of the nonzero-ideal class map selects a nonprincipal ideal "
                        + "from a nonidentity class. The unit ideal is principal, while the "
                        + "all-true theorem equates every one of their local readouts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-principality-observers-merge-a-global-gap"),
                DeclarationHandle.Create(Prefix + "local_principality_observers_are_blind"),
                H("All local readouts identify a principal and a nonprincipal ideal"),
                StatementSource.FromAuthor(BlindWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nonprincipal object is the existing norm-two ideal in the minus-five "
                        + "quadratic order; the principal comparison is the unit ideal. The "
                        + "existing local-global theorem supplies every local readout directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pid-degeneracy-removes-the-blindness-witness"),
                DeclarationHandle.Create(Prefix + "pid_blindness_witness_is_impossible"),
                H("The integer PID has trivial class group and no mixed pair"),
                StatementSource.FromAuthor(PidFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's class-number theorem gives class number one for the integers. "
                        + "Since every integer ideal is principal, the required principal versus "
                        + "nonprincipal pair cannot exist."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-zero-prime-does-not-give-a-dvr"),
                DeclarationHandle.Create(Prefix + "zero_prime_is_not_a_dvr"),
                H("Localization at the zero prime is not a DVR"),
                StatementSource.FromAuthor(ZeroPrimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a domain the zero-prime localization has zero maximal ideal, whereas a "
                        + "DVR has a nonzero maximal ideal. This records why the prime must be "
                        + "nonzero in the DVR theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-and-unit-ideal-degeneracies"),
                DeclarationHandle.Create(Prefix + "zero_and_unit_ideal_readouts_are_true"),
                H("Zero and unit ideals remain principal locally and globally"),
                StatementSource.FromAuthor(ZeroUnitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both degenerate ideals are globally principal and receive true local "
                        + "readouts. They therefore cannot supply the strict global witness."))),
                DescribeRole.Theorem))));

    private static Formula Readout(Formula prime, Formula ideal) =>
        Call("localPrincipalityReadout", prime, ideal);

    private static Formula LocalizedIdeal(Formula prime, Formula ideal) =>
        Call("localizedFractionalIdealAtPrime", prime, ideal);

    private static Formula LocalRing(Formula ring, Formula prime) =>
        Call("LocalizationAtPrime", ring, prime);

    private static Formula LocalizedIdealFormula()
    {
        Formula prime = F.Id("p");
        Formula ideal = F.Id("I");
        return Disp(Seq(
            LocalizedIdeal(prime, ideal), Sp, Eq, Sp,
            Call("ExtendedFractionalIdeal", ideal, LocalRing(F.Id("R"), prime)), Dot));
    }

    private static Formula ReadoutDefinitionFormula()
    {
        Formula prime = F.Id("p");
        Formula ideal = F.Id("I");
        return Disp(Seq(
            Readout(prime, ideal), Sp, Iff, Sp,
            Call("IsPrincipal", Call("IdealMap", ideal, LocalRing(F.Id("R"), prime))), Dot));
    }

    private static Formula DvrFormula()
    {
        Formula ring = F.Id("R");
        Formula prime = F.Id("p");
        return Disp(Seq(
            Call("IsDedekindDomain", ring), Sp, Land, Sp,
            Call("IsNonzeroPrime", prime), Sp, Rightarrow, RowBreak, Grp(),
            Call("IsDiscreteValuationRing", LocalRing(ring, prime)), Dot));
    }

    private static Formula FractionalPrincipalityFormula()
    {
        Formula prime = F.Id("p");
        Formula ideal = F.Id("I");
        return Disp(Seq(
            Forall, Sp, ideal, Comma, Sp,
            Call("IsPrincipal", LocalizedIdeal(prime, ideal)), Dot));
    }

    private static Formula ReadoutTrueFormula()
    {
        Formula prime = F.Id("p");
        Formula ideal = F.Id("I");
        return Disp(Seq(
            Forall, Sp, ideal, Comma, Sp,
            Readout(prime, ideal), Sp, Iff, Sp, F.Id("True"), Dot));
    }

    private static Formula BlindWitnessFormula()
    {
        Formula left = F.Id("I");
        Formula right = F.Id("J");
        Formula prime = F.Id("p");
        return Disp(Seq(
            Exists, Sp, left, Comma, Sp, right, Comma, RowBreak, Grp(),
            Neg, Sp, Call("IsPrincipal", left), Sp, Land, Sp,
            Call("IsPrincipal", right), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, prime, Comma, Sp,
            Readout(prime, left), Sp, Iff, Sp, Readout(prime, right), Close, Dot));
    }

    private static Formula AbstractBlindWitnessFormula()
    {
        Formula ring = F.Id("R");
        Formula left = F.Id("I");
        Formula right = F.Id("J");
        Formula prime = F.Id("p");
        return Disp(Seq(
            Call("IsDedekindDomain", ring), Sp, Land, Sp,
            Call("Nontrivial", Call("ClassGroup", ring)), Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, left, Comma, Sp, right, Comma, Sp,
            Neg, Sp, Call("IsPrincipal", left), Sp, Land, Sp,
            Call("IsPrincipal", right), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, prime, Comma, Sp,
            Readout(prime, left), Sp, Iff, Sp, Readout(prime, right), Close, Dot));
    }

    private static Formula PidFormula()
    {
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula left = F.Id("I");
        Formula right = F.Id("J");
        Formula prime = F.Id("p");
        Formula noPair = Seq(
            Neg, Sp, Exists, Sp, left, Comma, Sp, right, Comma, Sp,
            Neg, Sp, Call("IsPrincipal", left), Sp, Land, Sp,
            Call("IsPrincipal", right), Sp, Land, Sp,
            Open, Forall, Sp, prime, Comma, Sp,
            Readout(prime, left), Sp, Iff, Sp, Readout(prime, right), Close);
        return Disp(Seq(
            Call("ClassGroupCardinality", integers), Sp, Eq, Sp, D(1), Sp, Land,
            RowBreak, Grp(), noPair, Dot));
    }

    private static Formula ZeroPrimeFormula()
    {
        Formula ring = F.Id("R");
        return Disp(Seq(
            Neg, Sp, Call("IsDiscreteValuationRing", LocalRing(ring, D(0))), Dot));
    }

    private static Formula ZeroUnitFormula()
    {
        Formula prime = F.Id("p");
        Formula zeroIdeal = Call("ZeroIdeal", F.Id("R"));
        Formula unitIdeal = Call("UnitIdeal", F.Id("R"));
        return Disp(Seq(
            Call("IsPrincipal", zeroIdeal), Sp, Land, Sp,
            Call("IsPrincipal", unitIdeal), Sp, Land, RowBreak, Grp(),
            Readout(prime, zeroIdeal), Sp, Land, Sp, Readout(prime, unitIdeal), Dot));
    }
}
