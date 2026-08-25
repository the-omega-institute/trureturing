using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class BoundedIntegerCrtCompletenessDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PrimePowers/BoundedIntegerCrtCompleteness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power CRT has exactly its product capacity on bounded integers.",
        H("Bounded Integer CRT Completeness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-integer-crt-complete-iff"),
                DeclarationHandle.Create(Prefix + "bounded_integer_crt_complete_iff"),
                H("Bounded prime-power residues have exact product capacity"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The named boundedIntegerWindow is Fin N, hence consists of the N "
                            + "integers from zero through N minus one. It is not the inclusive "
                            + "interval from zero through N.")),
                    Paragraph(Text(
                        "The named primePowerResidueReading casts each bounded integer into "
                            + "every labeled prime-power residue ring. The modulus is the "
                            + "existing primePowerProduct from FiniteCrtJoin.")),
                    Paragraph(Text(
                        "The forward implication reuses the general retained-moduli capacity "
                            + "criterion. The reverse implication applies finite_crt_join and "
                            + "then uses the strict bounds carried by Fin N.")),
                    Paragraph(Text(
                        "The statement includes the empty window, empty prime support, and "
                            + "zero exponents. Empty support and all-zero exponents both have "
                            + "capacity one, so only windows of size at most one are faithful."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-support-condition-is-necessary"),
                DeclarationHandle.Create(Prefix + "prime_support_condition_is_necessary"),
                H("Overlapping composite moduli refute the unrestricted criterion"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With labels two and four and exponent one, the formal product is eight. "
                        + "Nevertheless zero and four already collide in both coordinates on "
                        + "the five-element window, so product capacity alone is insufficient."))),
                DescribeRole.Lemma))));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula ZModOf(Formula modulus) =>
        Seq(Operatorname, Grp(F.Id("ZMod")), Open, modulus, Close);

    private static Formula FinsetOf(Formula type) =>
        Seq(Operatorname, Grp(F.Id("Finset")), Open, type, Close);

    private static Formula PrimeSet(Formula set) =>
        Seq(Operatorname, Grp(F.Id("PrimeSet")), Open, set, Close);

    private static Formula InjectiveOf(Formula function) =>
        Seq(Operatorname, Grp(F.Id("Injective")), Open, function, Close);

    private static Formula IndexedProduct(
        Formula index, Formula indexSet, Formula factor) =>
        Seq(Prod, Underscore,
            Grp(index, Sp, InMacro, Sp, indexSet), Sp, factor);

    private static Formula ReadingType(
        Formula windowSize, Formula set, Formula readingExponent,
        Formula coordinateExponent)
    {
        Formula index = F.Id("p");
        Formula power = Power(index, coordinateExponent);
        Formula window = Seq(F.Id("X"), Underscore, Grp(windowSize));
        Formula factors = IndexedProduct(index, set, ZModOf(power));
        Formula reading = Seq(
            F.Id("q"), Underscore, Grp(set, Comma, Sp, readingExponent));
        return Seq(reading, Colon, Sp, new Formula.TypeArrow(window, factors));
    }

    private static Formula Product(Formula set, Formula exponentMap)
    {
        Formula index = F.Id("p");
        Formula exponent = Seq(exponentMap, Open, index, Close);
        return IndexedProduct(index, set, Power(index, exponent));
    }

    private static Formula MainFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula windowSize = F.Id("N");
        Formula set = F.Id("S");
        Formula kappa = F.Id("kappa");
        Formula exponentMap = new Formula.TypeArrow(naturals, naturals);
        Formula exponent = Seq(kappa, Open, F.Id("p"), Close);
        Formula reading = ReadingType(windowSize, set, kappa, exponent);
        return Disp(Seq(
            Forall, Sp, windowSize, Colon, Sp, naturals, Comma, Sp,
            set, Colon, Sp, FinsetOf(naturals), Comma, Sp,
            kappa, Colon, Sp, exponentMap, Comma, RowBreak, Grp(),
            PrimeSet(set), Sp, Rightarrow, Sp,
            InjectiveOf(reading), Sp, Iff, Sp,
            windowSize, Sp, Le, Sp, Product(set, kappa), Dot));
    }

    private static Formula NecessityFormula()
    {
        Formula labels = Seq(OpenBrace, D(2), Comma, Sp, D(4), CloseBrace);
        Formula exponent = D(1);
        Formula reading = ReadingType(D(5), labels, exponent, exponent);
        return Disp(Seq(
            Neg, Open, InjectiveOf(reading), Sp, Iff, Sp,
            D(5), Sp, Le, Sp, D(8), Close, Dot));
    }
}
