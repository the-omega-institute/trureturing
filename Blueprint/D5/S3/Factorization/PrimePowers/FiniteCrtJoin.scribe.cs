using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class FiniteCrtJoinDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PrimePowers/FiniteCrtJoin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime-power CRT retains empty support and labeled trivial factors.",
        H("Finite CRT Join"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-power-crt-join"),
                DeclarationHandle.Create(Prefix + "finite_crt_join"),
                H("Finite prime-power factors join by CRT"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a finite set of primes and let kappa assign a natural "
                            + "exponent to each prime. The named primePowerProduct is the "
                            + "product of the resulting prime powers.")),
                    Paragraph(Text(
                        "Pinned Mathlib's exact ZMod.prodEquivPi equivalence is applied to "
                            + "the subtype indexed by S. Nat.coprime_pow_primes discharges "
                            + "its pairwise-coprimality premise for distinct labels.")),
                    Paragraph(Text(
                        "Unlike ZMod.equivPi, this indexing retains primes whose exponent is "
                            + "zero. Those coordinates are ZMod 1 and therefore trivial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-crt-join-empty-support"),
                DeclarationHandle.Create(Prefix + "finite_crt_join_empty"),
                H("Empty support gives the trivial ring"),
                StatementSource.FromAuthor(EmptyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty product is one, and the dependent product over the empty "
                        + "index type is a trivial ring. The main equivalence covers this "
                        + "case without a nonemptiness hypothesis."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-crt-join-zero-exponent"),
                DeclarationHandle.Create(Prefix + "finite_crt_join_zero_exponent"),
                H("A zero exponent gives a trivial labeled coordinate"),
                StatementSource.FromAuthor(ZeroExponentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If kappa(p) is zero, the p-coordinate is ZMod 1 and is "
                        + "subsingleton. The global CRT equivalence remains valid with that "
                        + "label present."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-crt-join-singleton"),
                DeclarationHandle.Create(Prefix + "finite_crt_join_singleton"),
                H("A singleton family needs no primality premise"),
                StatementSource.FromAuthor(SingletonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Pairwise coprimality is vacuous for a singleton index type. Hence the "
                        + "singleton CRT equivalence holds for every natural label and every "
                        + "natural exponent, so no unused primality premise is retained."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-crt-join-all-zero-exponents"),
                DeclarationHandle.Create(Prefix + "finite_crt_join_all_zero_exponents"),
                H("All zero exponents still form a trivial product"),
                StatementSource.FromAuthor(AllZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the nonempty prime set containing two and three, assigning exponent "
                        + "zero to both labels gives modulus one and two labeled ZMod 1 "
                        + "coordinates. Both sides are trivial rings."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("prime-hypothesis-is-necessary"),
                DeclarationHandle.Create(Prefix + "prime_hypothesis_is_necessary"),
                H("Overlapping composite labels invalidate the unrestricted claim"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Dropping the prime-set condition admits labels two and four with exponent "
                        + "one. ZMod 8 cannot be ring-equivalent to ZMod 2 times ZMod 4: four "
                        + "vanishes in both target coordinates but not in ZMod 8."))),
                DescribeRole.Lemma))));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula ZModOf(Formula modulus) =>
        Seq(Operatorname, Grp(F.Id("ZMod")), Open, modulus, Close);

    private static Formula FinsetOf(Formula type) =>
        Seq(Operatorname, Grp(F.Id("Finset")), Open, type, Close);

    private static Formula PrimeSet(Formula set) =>
        Seq(Operatorname, Grp(F.Id("PrimeSet")), Open, set, Close);

    private static Formula SubsingletonOf(Formula type) =>
        Seq(Operatorname, Grp(F.Id("Subsingleton")), Open, type, Close);

    private static Formula NonemptyOf(Formula type) =>
        Seq(Operatorname, Grp(F.Id("Nonempty")), Open, type, Close);

    private static Formula RingEquiv(Formula source, Formula target) =>
        Seq(source, Sp, Sim, Sp, target);

    private static Formula IndexedProduct(
        Formula index, Formula indexSet, Formula factor) =>
        Seq(Prod, Underscore,
            Grp(index, Sp, InMacro, Sp, indexSet), Sp, factor);

    private static Formula CrtStatement(Formula set, Formula exponentMap)
    {
        Formula prime = F.Id("p");
        Formula exponent = At(exponentMap, prime);
        Formula power = Power(prime, exponent);
        Formula modulus = IndexedProduct(prime, set, power);
        Formula factors = IndexedProduct(prime, set, ZModOf(power));
        return NonemptyOf(RingEquiv(ZModOf(modulus), factors));
    }

    private static Formula MainFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula set = F.Id("S");
        Formula kappa = F.Id("kappa");
        Formula exponentMap = new Formula.TypeArrow(naturals, naturals);
        return Disp(Seq(
            Forall, Sp, set, Colon, Sp, FinsetOf(naturals), Comma, Sp,
            kappa, Colon, Sp, exponentMap, Comma, Sp,
            PrimeSet(set), Sp, Rightarrow, Sp, CrtStatement(set, kappa), Dot));
    }

    private static Formula EmptyFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula kappa = F.Id("kappa");
        Formula exponentMap = new Formula.TypeArrow(naturals, naturals);
        return Disp(Seq(
            Forall, Sp, kappa, Colon, Sp, exponentMap, Comma, Sp,
            CrtStatement(Seq(Emptyset), kappa), Dot));
    }

    private static Formula ZeroExponentFormula()
    {
        Formula set = F.Id("S");
        Formula kappa = F.Id("kappa");
        Formula prime = F.Id("p");
        Formula exponent = At(kappa, prime);
        return Disp(Seq(
            PrimeSet(set), Sp, Land, Sp,
            prime, Sp, InMacro, Sp, set, Sp, Land, Sp,
            exponent, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            CrtStatement(set, kappa), Sp, Land, Sp,
            SubsingletonOf(ZModOf(Power(prime, exponent))), Dot));
    }

    private static Formula SingletonFormula()
    {
        Formula prime = F.Id("p");
        Formula exponent = F.Id("e");
        Formula label = F.Id("q");
        Formula singleton = Seq(OpenBrace, prime, CloseBrace);
        Formula factor = ZModOf(Power(label, exponent));
        return Disp(Seq(
            Forall, Sp, prime, Comma, Sp, exponent, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp,
            NonemptyOf(RingEquiv(
                ZModOf(Power(prime, exponent)),
                IndexedProduct(label, singleton, factor))), Dot));
    }

    private static Formula AllZeroFormula()
    {
        Formula label = F.Id("p");
        Formula labels = Seq(OpenBrace, D(2), Comma, Sp, D(3), CloseBrace);
        return Disp(Seq(
            NonemptyOf(RingEquiv(
                ZModOf(D(1)),
                IndexedProduct(label, labels, ZModOf(D(1))))), Dot));
    }

    private static Formula NecessityFormula() => Disp(Seq(
        Neg, NonemptyOf(RingEquiv(
            ZModOf(D(8)),
            Seq(ZModOf(D(2)), Sp, Times, Sp, ZModOf(D(4))))), Dot));
}
