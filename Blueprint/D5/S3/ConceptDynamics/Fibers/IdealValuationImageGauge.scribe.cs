using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class IdealValuationImageGaugeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Fibers/IdealValuationImageGauge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer ideals separate faithfulness, image support, and generator gauge.",
        H("Ideal Valuation Faithfulness, Image, and Gauge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-ideal-valuations-are-faithful"),
                DeclarationHandle.Create(
                    Prefix + "int_ideal_valuation_readout_injective"),
                H("Prime-ideal valuations faithfully determine integer ideals"),
                StatementSource.FromAuthor(InjectivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The readout assigns the zero ideal top at every prime and assigns "
                            + "each nonzero ideal the prime exponents of its nonnegative "
                            + "canonical generator.")),
                    Paragraph(Text(
                        "Equality of the prime coordinates recovers the generator by unique "
                            + "factorization and then the ideal. This is a concrete theorem "
                            + "over the integers, not a general Dedekind-domain claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("infinite-support-family-is-outside-the-image"),
                DeclarationHandle.Create(
                    Prefix + "infinite_support_family_not_in_image"),
                H("An infinite-support exponent family is not realizable"),
                StatementSource.FromAuthor(ImageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The constant-one family is nonzero at every prime. For any nonzero "
                            + "integer ideal, a prime larger than its norm has exponent zero; "
                            + "the zero ideal instead has the constant-top readout.")),
                    Paragraph(Text(
                        "Thus even in the PID of integers the valuation image is not the full "
                            + "product. CompatibleResidueJointImage concerns the different map "
                            + "from integers to two residue rings and is not reused here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-generators-exhibit-unit-gauge"),
                DeclarationHandle.Create(Prefix + "two_generators_unit_gauge"),
                H("A principal ideal retains unit gauge"),
                StatementSource.FromAuthor(GaugeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The distinct integers 2 and -2 generate the same ideal, and the unit "
                            + "-1 carries one generator to the other. Principality therefore "
                            + "does not select a canonical signed generator.")),
                    Paragraph(Text(
                        "The degenerate audit also identifies the zero ideal's sole generator, "
                            + "the unit ideal's two generators, and the two generators of every "
                            + "integer prime ideal."))),
                DescribeRole.Theorem))));

    private static Formula Readout() => F.Id("vZ");

    private static Formula InfiniteFamily() => F.Id("oneAtEveryPrime");

    private static Formula ImageOfReadout() =>
        Seq(Operatorname, Grp(F.Id("range")), Open, Readout(), Close);

    private static Formula Span(Formula generator) =>
        Seq(Operatorname, Grp(F.Id("span")), Open, generator, Close);

    private static Formula InjectivityFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("Injective")), Open, Readout(), Close, Dot));

    private static Formula ImageFormula() => Disp(Seq(
        Neg, Open, InfiniteFamily(), Sp, InMacro, Sp, ImageOfReadout(), Close, Dot));

    private static Formula GaugeFormula()
    {
        Formula two = D(2);
        Formula minusTwo = Seq(Minus, D(2));
        Formula unit = F.Id("u");
        Formula integerUnits = F.Id("ZUnits");

        return Disp(Seq(
            two, Sp, Neq, Sp, minusTwo, Sp, Land, Sp,
            Span(two), Sp, Eq, Sp, Span(minusTwo), Sp, Land, RowBreak, Grp(),
            Exists, Sp, unit, Sp, InMacro, Sp, integerUnits, Comma, Sp,
            minusTwo, Sp, Eq, Sp, unit, Sp, Cdot, Sp, two, Dot));
    }
}
