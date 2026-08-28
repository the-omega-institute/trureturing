using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class SamePrimeScaleRedundancyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent scales at one base are redundant, unlike two distinct prime readings.",
        H("Same Prime Scale Redundancy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("old-layer-factors-through-new"),
                DeclarationHandle.Create(Prefix + "old_layer_factors_through_new"),
                H("The old layer is an explicit projection of the new layer"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The readout and projection are the existing primePowerReadout and "
                            + "primePowerProjection. The latter is Mathlib's ZMod.castHom.")),
                    Paragraph(Text(
                        "The imported vertical inverse-system theorem supplies compatibility "
                            + "at k <= k + 1. No primality assumption is used: the statement "
                            + "holds for every natural base, including zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjacent-joint-same-fiber"),
                DeclarationHandle.Create(Prefix + "adjacent_joint_same_fiber"),
                H("The adjacent joint and high layer have identical fibers"),
                StatementSource.FromAuthor(AdjacentFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equality of joint readings implies equality of their second "
                            + "coordinates. Conversely, equality at the high layer descends "
                            + "through the explicit projection to equality at the old layer.")),
                    Paragraph(Text(
                        "Thus the product interface induces exactly the high layer's fiber "
                            + "relation, not merely a one-way refinement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-precision-readout-is-constant"),
                DeclarationHandle.Create(Prefix + "zero_precision_readout_is_constant"),
                H("Precision zero is the single residue class"),
                StatementSource.FromAuthor(ZeroPrecisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At k = 0 the modulus is p to the zero, hence one. ZMod 1 is a "
                        + "singleton, so every pair of integers lies in the same fiber."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("two-adjacent-precision-fibers"),
                DeclarationHandle.Create(Prefix + "two_adjacent_precision_fibers"),
                H("The first two binary fibers are congruence modulo two and four"),
                StatementSource.FromAuthor(BinaryFibersFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For base two, equality at precision one means divisibility of the "
                        + "difference by two. Equality at precision two means divisibility "
                        + "by four. These are the concrete adjacent fibers requested."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("repeated-prime-pair-same-fiber"),
                DeclarationHandle.Create(Prefix + "repeated_prime_pair_same_fiber"),
                H("Repeating one prime gives a redundant diagonal pair"),
                StatementSource.FromAuthor(RepeatedPrimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the two prime labels coincide, the same-level pair repeats one "
                        + "coordinate. Its fiber relation is exactly the single coordinate's "
                        + "fiber relation."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("different-prime-joint-strictly-finer"),
                DeclarationHandle.Create(Prefix + "different_prime_joint_strictly_finer"),
                H("The mod two and mod three joint is strictly finer than either sensor"),
                StatementSource.FromAuthor(DifferentPrimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The joint kernel at p = 2, q = 3, and k = 1 is strictly contained "
                            + "in each single-coordinate kernel.")),
                    Paragraph(Text(
                        "Zero and two collide modulo two but separate modulo three. Zero and "
                            + "three collide modulo three but separate modulo two. These two "
                            + "named witnesses prove strictness in both directions."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Readout(Formula prime, Formula level) =>
        Subscript(F.Id("q"), Seq(prime, Comma, Sp, level));

    private static Formula Adjacent(Formula prime, Formula level) =>
        Subscript(F.Id("A"), Seq(prime, Comma, Sp, level));

    private static Formula SameLevelPair(
        Formula firstPrime, Formula secondPrime, Formula level) =>
        Subscript(
            F.Id("H"),
            Seq(firstPrime, Comma, Sp, secondPrime, Comma, Sp, level));

    private static Formula Kernel(Formula readout) =>
        Call("ker", readout);

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() =>
        Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula FactorizationFormula()
    {
        Formula prime = F.Id("p");
        Formula level = F.Id("k");
        Formula next = Seq(level, Plus, D(1));
        Formula projection = Subscript(
            F.Id("rho"),
            Seq(prime, Comma, Sp, next, Comma, Sp, level));
        return Disp(Seq(
            Forall, Sp, prime, Comma, Sp, level, Sp, InMacro, Sp, Naturals(), Comma,
            RowBreak, Grp(),
            Readout(prime, level), Sp, Eq, Sp,
            projection, Sp, Circ, Sp, Readout(prime, next), Dot));
    }

    private static Formula AdjacentFiberFormula()
    {
        Formula prime = F.Id("p");
        Formula level = F.Id("k");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula next = Seq(level, Plus, D(1));
        return Disp(Seq(
            Forall, Sp, prime, Comma, Sp, level, Sp, InMacro, Sp, Naturals(), Comma,
            Sp, x, Comma, Sp, y, Sp, InMacro, Sp, Integers(), Comma,
            RowBreak, Grp(),
            At(Adjacent(prime, level), x), Sp, Eq, Sp,
            At(Adjacent(prime, level), y), Sp, Iff, Sp,
            At(Readout(prime, next), x), Sp, Eq, Sp,
            At(Readout(prime, next), y), Dot));
    }

    private static Formula ZeroPrecisionFormula()
    {
        Formula prime = F.Id("p");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            x, Comma, Sp, y, Sp, InMacro, Sp, Integers(), Comma, Sp,
            At(Readout(prime, D(0)), x), Sp, Eq, Sp,
            At(Readout(prime, D(0)), y), Dot));
    }

    private static Formula BinaryFibersFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula difference = Seq(y, Minus, x);
        Formula modTwo = Seq(D(2), Sp, Mid, Sp, difference);
        Formula modFour = Seq(D(4), Sp, Mid, Sp, difference);
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, Integers(), Comma,
            RowBreak, Grp(), Open,
            At(Readout(D(2), D(1)), x), Sp, Eq, Sp,
            At(Readout(D(2), D(1)), y), Sp, Iff, Sp, modTwo, Close,
            Sp, Land, Sp, Open,
            At(Readout(D(2), D(2)), x), Sp, Eq, Sp,
            At(Readout(D(2), D(2)), y), Sp, Iff, Sp, modFour, Close, Dot));
    }

    private static Formula RepeatedPrimeFormula()
    {
        Formula prime = F.Id("p");
        Formula level = F.Id("k");
        return Disp(Seq(
            Forall, Sp, prime, Comma, Sp, level, Sp, InMacro, Sp, Naturals(), Comma,
            RowBreak, Grp(),
            Kernel(SameLevelPair(prime, prime, level)), Sp, Eq, Sp,
            Kernel(Readout(prime, level)), Dot));
    }

    private static Formula DifferentPrimeFormula()
    {
        Formula joint = Kernel(SameLevelPair(D(2), D(3), D(1)));
        return Disp(Seq(
            joint, Sp, Subset, Sp, Kernel(Readout(D(2), D(1))),
            Sp, Land, Sp,
            joint, Sp, Subset, Sp, Kernel(Readout(D(3), D(1))), Dot));
    }
}
