using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Periods;

internal sealed class CrtPeriodCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Periods/CrtPeriodComposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power CRT coordinates compose the phase period by least common multiple.",
        H("CRT Period Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phase-period-crt-composition"),
                DeclarationHandle.Create(Prefix + "phase_period_crt_composition"),
                H("Prime-power periods compose by lcm"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonzero natural modulus, its named phase period is the "
                            + "least common multiple of the periods of the prime powers in "
                            + "its canonical factorization.")),
                    Paragraph(Text(
                        "The imported finite CRT supplies the ring equivalence. Additive "
                            + "order is invariant under that equivalence, and the order of "
                            + "a finite dependent product is the lcm of coordinate orders.")),
                    Paragraph(Text(
                        "Primality carries the CRT coprimality argument. The special role of "
                            + "two occurs only inside the already named local period formula "
                            + "T(m)=m/gcd(m,2)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonzero-modulus-is-necessary"),
                DeclarationHandle.Create(Prefix + "nonzero_modulus_is_necessary"),
                H("The zero modulus is necessarily excluded"),
                StatementSource.FromAuthor(ZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At zero the named period is zero, while primeFactors zero is empty and "
                        + "the Finset lcm of an empty family is one. Thus the nonzero premise "
                        + "cannot be removed from the canonical-factorization statement."))),
                DescribeRole.Lemma)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Factorization/PrimePowers/FiniteCrtJoin")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod")),
        ]));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula PeriodAt(Formula modulus) =>
        At(F.Id("T"), modulus);

    private static Formula PrimeFactorsOf(Formula modulus) =>
        Seq(Operatorname, Grp(F.Id("PrimeFactors")), Open, modulus, Close);

    private static Formula ValuationAt(Formula prime, Formula modulus) =>
        Seq(Sub(F.Id("v"), prime), Open, modulus, Close);

    private static Formula LocalPeriod(Formula prime, Formula modulus) =>
        PeriodAt(Power(prime, ValuationAt(prime, modulus)));

    private static Formula PeriodLcm(Formula modulus)
    {
        Formula prime = F.Id("p");
        return Seq(
            Operatorname, Grp(F.Id("lcm")), Underscore,
            Grp(prime, Sp, InMacro, Sp, PrimeFactorsOf(modulus)), Sp,
            LocalPeriod(prime, modulus));
    }

    private static Formula MainFormula()
    {
        Formula modulus = F.Id("m");
        return Disp(Seq(
            Forall, Sp, modulus, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            modulus, Neq, D(0), Sp, Rightarrow, Sp,
            PeriodAt(modulus), Eq, PeriodLcm(modulus), Dot));
    }

    private static Formula ZeroFormula()
    {
        Formula zero = D(0);
        return Disp(Seq(
            Neg, Grp(PeriodAt(zero), Eq, PeriodLcm(zero)), Dot));
    }
}
