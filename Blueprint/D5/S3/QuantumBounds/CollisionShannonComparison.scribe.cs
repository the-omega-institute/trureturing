using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class CollisionShannonComparisonDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/QuantumBounds/CollisionShannonComparison.";

    private static Formula At(Formula family, Formula index) => F.Seq(
        family, F.Open, index, F.Close);

    private static Formula FiniteSum(Formula index, Formula summand) => F.Seq(
        F.Sum, F.Sp, F.Underscore, F.Grp(index), F.Sp, summand);

    private static Formula CollisionEntropy(Formula law, Formula index) => F.Seq(
        F.Minus, F.Log, F.Sp, F.Open,
        FiniteSum(index, F.Seq(At(law, index), F.Caret, F.Grp(F.D(2)))),
        F.Close);

    private static Formula ShannonEntropy(Formula law) => F.Seq(
        F.Id("H"), F.Open, law, F.Close);

    private static Formula ProbabilityAssumptions(Formula law, Formula index) => F.Seq(
        F.Open,
        F.Open,
        F.Forall, F.Sp, index, F.Comma, F.Sp,
        F.D(0), F.Sp, F.Le, F.Sp, At(law, index),
        F.Close, F.Sp, F.Land, F.RowBreak,
        FiniteSum(index, At(law, index)), F.Sp, F.Eq, F.Sp, F.D(1),
        F.Close);

    private static Formula EntropyEquality(Formula law, Formula index) => F.Seq(
        CollisionEntropy(law, index), F.Sp, F.Eq, F.Sp, ShannonEntropy(law));

    private static Formula UniformOnPositiveSupport(
        Formula law,
        Formula firstIndex,
        Formula secondIndex) => F.Seq(
            F.Forall, F.Sp, firstIndex, F.Sp, secondIndex, F.Comma, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, At(law, firstIndex),
            F.Sp, F.Rightarrow, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, At(law, secondIndex),
            F.Sp, F.Rightarrow, F.Sp,
            At(law, firstIndex), F.Sp, F.Eq, F.Sp, At(law, secondIndex));

    private static Formula UniformEverywhere(
        Formula law,
        Formula firstIndex,
        Formula secondIndex) => F.Seq(
            F.Forall, F.Sp, firstIndex, F.Sp, secondIndex, F.Comma, F.Sp,
            At(law, firstIndex), F.Sp, F.Eq, F.Sp, At(law, secondIndex));

    private static Formula Statement(
        Formula law,
        Formula index,
        Formula conclusion) => F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp, F.Iota, F.Esc,
            F.OpenBracket,
            F.Operatorname, F.Grp(F.Id("Fintype")), F.Open, F.Iota, F.Close,
            F.CloseBracket, F.Comma, F.RowBreak,
            F.Forall, F.Sp, law, F.Colon, F.Sp,
            F.Iota, F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.RowBreak,
            ProbabilityAssumptions(law, index), F.Sp, F.Rightarrow, F.RowBreak,
            conclusion, F.Dot,
            F.End, F.Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The order-two collision expression is bounded by Shannon entropy, with equality exactly at laws uniform on their positive support.",
        H("Collision Entropy versus Shannon Entropy"),
        Blocks(
            Paragraph(Text(
                "The frozen CollisionEntropyUncertainty proof already contained this comparison "
                + "as an internal have: each measurement law has Shannon entropy at least minus "
                + "the logarithm of its squared-mass sum. That local fact was unavailable outside "
                + "the enclosing proof. The present module re-establishes the Jensen argument as "
                + "a top-level theorem and adds its equality characterization.")),
            Paragraph(Text(
                "The equality condition is pairwise equality on positive support, not uniformity "
                + "over every index. A point mass on a carrier with at least two indices attains "
                + "equality: its squared-mass sum is one and H is zero, but it is not uniform "
                + "across the full carrier. A full-index uniformity biconditional would therefore "
                + "be false. The theorem name collision_entropy_eq_shannon_entropy_iff_uniform_on_support "
                + "records the exact condition, whereas collision_entropy_eq_shannon_entropy_of_uniform "
                + "states full-index uniformity only as a sufficient condition.")),
            Paragraph(Text(
                "The proof replaces every zero mass by the positive logarithm argument one and "
                + "then applies weighted logarithmic Jensen. Strict concavity identifies equality "
                + "only among coordinates carrying nonzero weight, which is precisely the positive "
                + "support because the law is nonnegative. Normalization rules out an empty carrier, "
                + "so no separate nonemptiness assumption is required.")),
            Paragraph(Text(
                "This module treats only the order-two collision expression -log(SUM p(i)^2). "
                + "It does not state general Renyi-entropy monotonicity.")),
            Paragraph(Text(
                "All three displays are authored legally because the current statement projector "
                + "has no pinned projectable fixture for these declarations. Document construction "
                + "therefore records a ProjectionGap for each theorem.")),
            Describe.Lean(
                DescribeId.Create("order-two-collision-entropy-is-at-most-shannon-entropy"),
                DeclarationHandle.Create(
                    LeanPrefix + "collision_entropy_le_shannon_entropy"),
                H("Order-two collision entropy is at most Shannon entropy"),
                StatementSource.FromAuthor(Statement(
                    F.Id("p"),
                    F.Id("i"),
                    F.Seq(
                        CollisionEntropy(F.Id("p"), F.Id("i")),
                        F.Sp, F.Le, F.Sp,
                        ShannonEntropy(F.Id("p"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite nonnegative law of total mass one, the theorem exports the "
                        + "comparison that was previously confined to the uncertainty proof. The "
                        + "zero-mass substitution contributes neither to the weighted logarithmic "
                        + "sum nor to the squared-mass sum, while making every logarithm argument "
                        + "strictly positive. Negating the resulting concave Jensen inequality gives "
                        + "the displayed lower bound for H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("collision-shannon-equality-is-uniformity-on-positive-support"),
                DeclarationHandle.Create(
                    LeanPrefix + "collision_entropy_eq_shannon_entropy_iff_uniform_on_support"),
                H("Collision-Shannon equality is uniformity on positive support"),
                StatementSource.FromAuthor(Statement(
                    F.Id("p"),
                    F.Id("i"),
                    F.Seq(
                        F.Open,
                        EntropyEquality(F.Id("p"), F.Id("i")),
                        F.Close, F.Sp, F.Leftrightarrow, F.RowBreak,
                        UniformOnPositiveSupport(
                            F.Id("p"), F.Id("i"), F.Id("j"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equality of the two entropy expressions is rewritten as equality in the "
                        + "weighted logarithmic Jensen step. The strict-concavity equality criterion "
                        + "then equates the substituted logarithm arguments exactly where their "
                        + "weights are nonzero. Nonnegativity converts nonzero mass into positive "
                        + "mass, yielding pairwise equality on positive support in both directions "
                        + "without imposing any condition on zero coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-index-uniformity-suffices-for-collision-shannon-equality"),
                DeclarationHandle.Create(
                    LeanPrefix + "collision_entropy_eq_shannon_entropy_of_uniform"),
                H("Full-index uniformity suffices for Collision-Shannon equality"),
                StatementSource.FromAuthor(Statement(
                    F.Id("p"),
                    F.Id("i"),
                    F.Seq(
                        F.Open,
                        UniformEverywhere(F.Id("p"), F.Id("i"), F.Id("j")),
                        F.Close, F.Sp, F.Rightarrow, F.RowBreak,
                        EntropyEquality(F.Id("p"), F.Id("i"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Uniformity on the entire finite index type immediately supplies pairwise "
                        + "equality on positive support. The sufficient theorem applies the reverse "
                        + "direction of the preceding biconditional. Its one-way form is essential: "
                        + "zero coordinates prevent full-index uniformity from being necessary."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Entropy/MaxEntropy"))]));
}
