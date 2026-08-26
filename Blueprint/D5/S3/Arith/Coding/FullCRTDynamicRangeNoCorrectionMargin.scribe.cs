using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class FullCRTDynamicRangeNoCorrectionMarginDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Coding/FullCRTDynamicRangeNoCorrectionMargin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Using the full CRT product gives exact distance one, with the degenerate "
            + "boundaries and the role of full capacity made explicit.",
        H("Full CRT Dynamic Range Has No Correction Margin"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximum-distance-is-controlled-by-the-first-modulus"),
                DeclarationHandle.Create(
                    Prefix + "maximum_possible_distance_iff_first_modulus_bound"),
                H("Maximum distance is controlled by the first modulus"),
                StatementSource.FromAuthor(MaximumDistanceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Specializing the existing dynamic-range equivalence to d=n leaves a "
                        + "prefix of length one. This audits the largest possible Hamming "
                        + "distance without introducing a new distance argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-crt-range-has-minimum-distance-one"),
                DeclarationHandle.Create(
                    Prefix + "full_crt_dynamic_range_minimum_distance"),
                H("Full CRT range has minimum distance one"),
                StatementSource.FromAuthor(FullRangeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At distance one the dynamic-range theorem returns the full prefix "
                            + "product itself, so the minimum distance is at least one.")),
                    Paragraph(Text(
                        "For at least two coordinates, the last modulus being above one makes "
                            + "the full product strictly exceed the preceding prefix, and the "
                            + "same theorem rules out distance two. A single coordinate is "
                            + "handled by the ambient one-coordinate Hamming bound.")),
                    Paragraph(Text(
                        "The source's t(K) clause is not represented because the volume does "
                            + "not define t with that meaning; no replacement definition is "
                            + "invented here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-length-is-necessary"),
                DeclarationHandle.Create(Prefix + "positive_length_is_necessary"),
                H("Positive length is necessary"),
                StatementSource.FromAuthor(ZeroLengthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At length zero all indexed modulus assumptions are vacuous. The full "
                        + "prefix product is one, so there are no two messages and the defined "
                        + "minimum-distance infimum is zero rather than one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moduli-above-one-are-necessary"),
                DeclarationHandle.Create(
                    Prefix + "modulus_greater_than_one_is_necessary"),
                H("Moduli above one are necessary"),
                StatementSource.FromAuthor(UnitModulusFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A one-coordinate code with modulus one has full product one. Its full "
                        + "message range contains no distinct pair, so its minimum-distance "
                        + "object is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pairwise-coprimality-is-necessary"),
                DeclarationHandle.Create(Prefix + "pairwise_coprime_is_necessary"),
                H("Pairwise coprimality is necessary"),
                StatementSource.FromAuthor(NoncoprimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordered moduli two and four are both above one, but messages zero "
                        + "and four have the same two residues. The full-product code therefore "
                        + "has minimum distance zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-dynamic-range-is-necessary"),
                DeclarationHandle.Create(Prefix + "full_dynamic_range_is_necessary"),
                H("Full dynamic range is necessary"),
                StatementSource.FromAuthor(ShortRangeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For coprime moduli two and three, restricting messages to zero and one "
                        + "uses a range of two below the full product six. Those two words "
                        + "differ in both coordinates, so the exact minimum distance is two."))),
                DescribeRole.Theorem))));

    private static Formula MaximumDistanceFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula range = F.Id("K");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        return Disp(Seq(
            Forall, Sp, m, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            n, Comma, Sp, range, Sp, InMacro, Sp, naturals, Comma, Sp,
            OrderedCoprimePremises(m, n, positiveAboveOne: false),
            Sp, Rightarrow, Sp,
            Call("MinDistanceAtLeast", m, n, range, n),
            Sp, Iff, Sp, range, Sp, Leq, Sp, Call("prefixProduct", m, D(1)), Dot));
    }

    private static Formula FullRangeFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula fullRange = Call("prefixProduct", m, n);
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        return Disp(Seq(
            Forall, Sp, m, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            n, Sp, InMacro, Sp, naturals, Comma, Sp,
            OrderedCoprimePremises(m, n, positiveAboveOne: true),
            Sp, Rightarrow, Sp,
            Call("residueMinimumDistance", m, n, fullRange), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula ZeroLengthFormula()
    {
        Formula constantTwo = OpenLambda(F.Id("i"), D(2));
        Formula range = Call("prefixProduct", constantTwo, D(0));

        return Disp(Seq(
            Call("residueMinimumDistance", constantTwo, D(0), range),
            Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula UnitModulusFormula()
    {
        Formula constantOne = OpenLambda(F.Id("i"), D(1));
        Formula range = Call("prefixProduct", constantOne, D(1));

        return Disp(Seq(
            Call("residueMinimumDistance", constantOne, D(1), range),
            Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula NoncoprimeFormula()
    {
        Formula m = F.Id("m");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula fullRange = Call("prefixProduct", m, D(2));

        return Disp(Seq(
            Exists, Sp, m, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            Open, Forall, Sp, i, Comma, Sp, i, Sp, Lt, Sp, D(2), Sp,
            Rightarrow, Sp, D(1), Sp, Lt, Sp, Call("m", i), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Leq, Sp, j, Sp, Land, Sp, j, Sp, Lt, Sp, D(2), Sp,
            Rightarrow, Sp, Call("m", i), Sp, Leq, Sp, Call("m", j), Close,
            Sp, Land, Sp,
            Neg, Call("Coprime", Call("m", D(0)), Call("m", D(1))),
            Sp, Land, Sp,
            Call("residueMinimumDistance", m, D(2), fullRange),
            Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula ShortRangeFormula()
    {
        Formula m = F.Id("m");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula fullRange = Call("prefixProduct", m, D(2));

        return Disp(Seq(
            Exists, Sp, m, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            Open, Forall, Sp, i, Comma, Sp, i, Sp, Lt, Sp, D(2), Sp,
            Rightarrow, Sp, D(1), Sp, Lt, Sp, Call("m", i), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Leq, Sp, j, Sp, Land, Sp, j, Sp, Lt, Sp, D(2), Sp,
            Rightarrow, Sp, Call("m", i), Sp, Leq, Sp, Call("m", j), Close,
            Sp, Land, Sp,
            Call("Coprime", Call("m", D(0)), Call("m", D(1))), Sp, Land, Sp,
            D(2), Sp, Lt, Sp, fullRange, Sp, Land, Sp,
            Call("residueMinimumDistance", m, D(2), D(2)),
            Sp, Eq, Sp, D(2), Dot));
    }

    private static Formula OrderedCoprimePremises(
        Formula m,
        Formula n,
        bool positiveAboveOne)
    {
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula lower = positiveAboveOne ? D(1) : D(0);

        return Seq(
            D(0), Sp, Lt, Sp, n, Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Leq, Sp, j, Sp, Land, Sp, j, Sp, Lt, Sp, n, Sp,
            Rightarrow, Sp, Call("m", i), Sp, Leq, Sp, Call("m", j), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp, i, Sp, Lt, Sp, n, Sp,
            Rightarrow, Sp, lower, Sp, Lt, Sp, Call("m", i), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Lt, Sp, n, Sp, Land, Sp, j, Sp, Lt, Sp, n, Sp, Land, Sp,
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            Call("Coprime", Call("m", i), Call("m", j)), Close);
    }

    private static Formula OpenLambda(Formula variable, Formula value) =>
        Seq(Open, variable, Sp, Mapsto, Sp, value, Close);
}
