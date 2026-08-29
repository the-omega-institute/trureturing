using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class PrimeObservationDepthGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power depth and prime-prefix depth meet the same information lower bound, "
            + "while an explicit equal-storage example separates their fault geometry.",
        H("Prime Observation Depth and Geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("horizontal-cardinality-depth-is-least"),
                DeclarationHandle.Create(Prefix + "horizontal_cardinality_depth_isLeast"),
                H("Horizontal cardinality depth is least"),
                StatementSource.FromAuthor(HorizontalLeastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing horizontal depth uses the inclusive interval from zero "
                        + "through its argument. Evaluating it at N minus one gives the least "
                        + "prime-prefix length whose product is at least the cardinality N."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("vertical-prime-power-depth-is-least"),
                DeclarationHandle.Create(Prefix + "vertical_depth_isLeast"),
                H("Vertical prime-power depth is least"),
                StatementSource.FromAuthor(VerticalLeastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a base greater than one, verticalDepth is the least natural exponent "
                        + "whose prime-power capacity reaches the requested window size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("vertical-depth-is-the-ceiling-logarithm"),
                DeclarationHandle.Create(Prefix + "vertical_depth_eq_natCeil_logb"),
                H("Vertical depth is the ceiling logarithm"),
                StatementSource.FromAuthor(VerticalCeilingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib identifies its natural upper logarithm with the natural ceiling "
                        + "of the totalized real logarithm, including zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("horizontal-and-vertical-bit-cost-lower-bounds"),
                DeclarationHandle.Create(
                    Prefix + "horizontal_vertical_bit_cost_lower_bounds"),
                H("Horizontal and vertical bit costs meet the capacity bound"),
                StatementSource.FromAuthor(BitBoundsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The horizontal sum is the base-two logarithm of the selected initial "
                            + "prime product. Its least-depth capacity bound therefore yields "
                            + "the horizontal information lower bound.")),
                    Paragraph(Text(
                        "For N at least two, the generic finite-prime information theorem is "
                            + "applied to the singleton prime with precision verticalDepth. "
                            + "The zero- and one-state windows are checked separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("base-greater-than-one-is-necessary"),
                DeclarationHandle.Create(Prefix + "base_gt_one_is_necessary"),
                H("A base greater than one is necessary"),
                StatementSource.FromAuthor(BaseNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At base one and window size two, no exponent reaches the window and the "
                        + "claimed logarithmic cost is zero. This concrete counterexample "
                        + "certifies the only nondefinition hypothesis used by the depth law."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("equal-bit-cost-has-different-fault-geometry"),
                DeclarationHandle.Create(Prefix + "same_bit_cost_different_fault_geometry"),
                H("Equal bit cost has different fault geometry"),
                StatementSource.FromAuthor(FaultGeometryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A single modulus-eight channel and separate modulus-two and "
                            + "modulus-three channels each require three rounded storage bits.")),
                    Paragraph(Text(
                        "The prime pair has distance at least one on the six-state window. "
                            + "Removing the modulus-two coordinate still separates zero from "
                            + "two, whereas removing the sole modulus-eight coordinate hides "
                            + "that pair completely."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula PrimeType() =>
        Seq(Operatorname, Grp(F.Id("NatPrimes")));

    private static Formula HorizontalDepth(Formula window) =>
        Call("horizontalCardinalityDepth", window);

    private static Formula VerticalDepth(Formula prime, Formula window) =>
        Call("verticalDepth", prime, window);

    private static Formula PrefixProduct(Formula depth) =>
        Call("primePrefixProduct", depth);

    private static Formula Logb(Formula basis, Formula value) =>
        Call("logb", basis, value);

    private static Formula HorizontalLeastFormula()
    {
        Formula window = F.Id("N");
        Formula depth = F.Id("r");
        Formula candidates = Seq(
            OpenBrace, depth, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            window, Sp, Leq, Sp, PrefixProduct(depth), CloseBrace);
        return Disp(Seq(
            Forall, Sp, window, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Call("IsLeast", candidates, HorizontalDepth(window)), Dot));
    }

    private static Formula VerticalLeastFormula()
    {
        Formula prime = F.Id("p");
        Formula window = F.Id("N");
        Formula depth = F.Id("k");
        Formula candidates = Seq(
            OpenBrace, depth, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            window, Sp, Leq, Sp, new Formula.Power(prime, depth), CloseBrace);
        return Disp(Seq(
            Forall, Sp, prime, Comma, Sp, window, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            D(1), Sp, Lt, Sp, prime, Sp, Rightarrow, Sp,
            Call("IsLeast", candidates, VerticalDepth(prime, window)), Dot));
    }

    private static Formula VerticalCeilingFormula()
    {
        Formula prime = F.Id("p");
        Formula window = F.Id("N");
        return Disp(Seq(
            Forall, Sp, prime, Comma, Sp, window, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            VerticalDepth(prime, window), Sp, Eq, Sp,
            Call("natCeil", Logb(prime, window)), Dot));
    }

    private static Formula BitBoundsFormula()
    {
        Formula prime = F.Id("p");
        Formula window = F.Id("N");
        Formula depth = HorizontalDepth(window);
        Formula horizontalCost = Call("horizontalBitCost", depth);
        Formula verticalCost = Call("verticalBitCost", prime, window);
        Formula windowBits = Logb(D(2), window);
        Formula equality = Seq(
            horizontalCost, Sp, Eq, Sp, Logb(D(2), PrefixProduct(depth)));
        Formula horizontalBound = Seq(windowBits, Sp, Leq, Sp, horizontalCost);
        Formula verticalBound = Seq(windowBits, Sp, Leq, Sp, verticalCost);
        return Disp(Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, PrimeType(), Comma, Sp,
            window, Sp, InMacro, Sp, Naturals(), Comma, RowBreak, Grp(),
            equality, Sp, Land, Sp, horizontalBound, Sp, Land, Sp, verticalBound, Dot));
    }

    private static Formula BaseNecessityFormula()
    {
        Formula depth = VerticalDepth(D(1), D(2));
        Formula candidates = Seq(
            OpenBrace, F.Id("k"), Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            D(2), Sp, Leq, Sp, new Formula.Power(D(1), F.Id("k")), CloseBrace);
        return Disp(Seq(
            Neg, Sp, Call("IsLeast", candidates, depth), Sp, Land, Sp,
            Neg, Sp, Open, Logb(D(2), D(2)), Sp, Leq, Sp,
            Call("verticalBitCost", D(1), D(2)), Close, Dot));
    }

    private static Formula FaultGeometryFormula()
    {
        Formula vertical = F.Id("verticalModuli");
        Formula horizontal = F.Id("horizontalModuli");
        Formula sameCost = Seq(
            Call("storedChannelBitCost", vertical, D(1)), Sp, Eq, Sp,
            Call("storedChannelBitCost", horizontal, D(2)));
        Formula distance = Call("MinDistanceAtLeast", horizontal, D(2), D(6), D(1));
        Formula verticalBlind = Call(
            "AgreeOutside", vertical, D(1), D(0), D(0), D(2));
        Formula horizontalDetects = Seq(
            Neg, Sp, Call("AgreeOutside", horizontal, D(2), D(0), D(0), D(2)));
        return Disp(Seq(
            sameCost, Sp, Land, Sp, distance, Sp, Land, Sp,
            verticalBlind, Sp, Land, Sp, horizontalDetects, Dot));
    }
}
