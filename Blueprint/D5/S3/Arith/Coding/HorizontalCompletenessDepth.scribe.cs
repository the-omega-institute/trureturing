using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class HorizontalCompletenessDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint residues modulo an initial prime segment separate a bounded natural interval "
            + "exactly when the segment's modulus product exceeds the interval, and the first "
            + "such segment is its horizontal completeness depth.",
        H("Horizontal Completeness Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-prefix-residues-separate-exactly-below-their-product"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/HorizontalCompletenessDepth."
                        + "residue_reading_injOn_iff_primorial_gt"),
                H("Prime-prefix residues separate exactly below their product"),
                StatementSource.FromAuthor(InjectivityThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The depth-r reading records a natural number modulo each of the first "
                            + "r primes. On the interval from zero through N, this joint reading "
                            + "is injective exactly when the product of those primes is greater "
                            + "than N; the empty prefix is included with product one.")),
                    Paragraph(Text(
                        "If the product is at most N, zero and the positive prefix product are "
                            + "distinct points of the interval with the same residue in every "
                            + "coordinate. Conversely, equality of all coordinates and pairwise "
                            + "coprimality give congruence modulo the entire product, and two "
                            + "numbers below that product with this congruence must coincide."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("some-prime-prefix-product-exceeds-every-natural-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/HorizontalCompletenessDepth."
                        + "exists_primePrefixProduct_gt"),
                H("Some prime-prefix product exceeds every natural bound"),
                StatementSource.FromAuthor(PrefixProductExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every natural bound N is exceeded by the product of some finite initial "
                            + "segment of the primes. The proof chooses the segment of length N: "
                            + "each of its prime factors is at least two, so its product is at "
                            + "least 2 to the N, which is strictly greater than N.")),
                    Paragraph(Text(
                        "This existence result makes the least successful depth well-defined for "
                            + "every bounded natural interval, including the zero bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("horizontal-depth-is-the-least-faithful-prime-residue-depth"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/HorizontalCompletenessDepth."
                        + "horizontal_completeness_depth"),
                H("Horizontal depth is the least faithful prime-residue depth"),
                StatementSource.FromAuthor(HorizontalDepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each N, horizontalDepth N is the least number of initial prime "
                            + "coordinates whose joint residue reading is injective on the "
                            + "natural interval from zero through N.")),
                    Paragraph(Text(
                        "The depth is defined as the first prime-prefix product greater than N. "
                            + "The injectivity threshold identifies that same condition with "
                            + "faithfulness on the interval, so the selected depth is faithful "
                            + "and no smaller faithful depth can exist."))),
                DescribeRole.Theorem))));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula ClosedInterval(Formula bound) =>
        Seq(OpenBracket, D(0), Comma, Sp, bound, CloseBracket);

    private static Formula PrimePrefixProduct(Formula depth) =>
        Call("primePrefixProduct", depth);

    private static Formula ResidueReading(Formula depth) =>
        Call("residueReading", depth);

    private static Formula InjectiveOnWindow(Formula depth, Formula bound) =>
        Call("InjOn", ResidueReading(depth), ClosedInterval(bound));

    private static Formula InjectivityThresholdFormula()
    {
        Formula bound = F.Id("N");
        Formula depth = F.Id("r");

        return Disp(Seq(
            Forall, Sp, bound, Comma, Sp, depth, Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
            InjectiveOnWindow(depth, bound), Sp, Iff, Sp,
            bound, Sp, Lt, Sp, PrimePrefixProduct(depth), Dot));
    }

    private static Formula PrefixProductExistenceFormula()
    {
        Formula bound = F.Id("N");
        Formula depth = F.Id("r");

        return Disp(Seq(
            Forall, Sp, bound, Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
            Exists, Sp, depth, Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
            bound, Sp, Lt, Sp, PrimePrefixProduct(depth), Dot));
    }

    private static Formula HorizontalDepthFormula()
    {
        Formula bound = F.Id("N");
        Formula depth = F.Id("r");
        Formula faithfulDepths = Seq(
            OpenBrace, depth, Sp, InMacro, Sp, NaturalNumbers(), Sp, Mid, Sp,
            InjectiveOnWindow(depth, bound), CloseBrace);

        return Disp(Seq(
            Forall, Sp, bound, Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
            Call("IsLeast", faithfulDepths, Call("horizontalDepth", bound)), Dot));
    }
}
