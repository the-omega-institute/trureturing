using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class WeightedJointUltrapseudometricDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted joint observation distance has a strong triangle law, an exact kernel, "
            + "and a separated quotient.",
        H("Weighted Joint Ultrapseudometric and Zero Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("selected-joint-readout"),
                DeclarationHandle.Create(Prefix + "selectedJointReadout"),
                H("Selected readouts form one joint observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite budget J restricts the canonical dependent jointReadout to "
                        + "the selected coordinates. This is the formal q_J from the source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-observation-kernel-setoid"),
                DeclarationHandle.Create(Prefix + "jointObservationSetoid"),
                H("Joint observation equality defines the kernel relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The observation relation is the kernel Setoid of the selected joint "
                        + "readout, so related states have every selected coordinate equal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-observation-quotient"),
                DeclarationHandle.Create(Prefix + "JointObservationQuotient"),
                H("The observation quotient identifies the joint kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quotienting by the joint observation Setoid gives the carrier on which "
                        + "zero distance will separate equivalence classes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-joint-ultrapseudometric"),
                DeclarationHandle.Create(Prefix + "weighted_joint_ultrapseudometric"),
                H("Nonnegative weights give the strong triangle inequality"),
                StatementSource.FromAuthor(UltrametricFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nonempty budget, Finset.sup'_le reduces the claim to one "
                            + "coordinate. The discrete strong triangle law is multiplied by "
                            + "the nonnegative coordinate weight, and Finset.le_sup' embeds "
                            + "both resulting terms into their joint suprema.")),
                    Paragraph(Text(
                        "The empty budget has distance zero. Nonnegativity is explicit because "
                            + "the source omits it even though multiplication by a negative "
                            + "weight reverses the required order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-joint-zero-distance-kernel"),
                DeclarationHandle.Create(Prefix + "weighted_joint_zero_distance_iff"),
                H("Zero distance is equality of every selected readout"),
                StatementSource.FromAuthor(ZeroKernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Strict positivity makes every unequal selected coordinate contribute "
                            + "a positive term, so a zero supremum forces coordinate equality.")),
                    Paragraph(Text(
                        "Conversely, coordinate equality makes every term zero. The result also "
                            + "covers an empty index type or empty budget, where both sides are "
                            + "vacuously zero or true."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonnegative-weights-are-necessary"),
                DeclarationHandle.Create(Prefix + "nonnegative_weights_are_necessary"),
                H("A negative weight breaks the strong triangle law"),
                StatementSource.FromAuthor(NegativeWeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a singleton Unit budget with weight minus one and identity Boolean "
                        + "readout, the path false, true, false makes the claimed inequality "
                        + "reduce to zero less than or equal to minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strictly-positive-weights-are-necessary"),
                DeclarationHandle.Create(Prefix + "strictly_positive_weights_are_necessary"),
                H("A zero weight breaks the zero kernel"),
                StatementSource.FromAuthor(ZeroWeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A singleton coordinate of weight zero assigns distance zero to the "
                        + "distinct Boolean states false and true. Nonnegativity therefore does "
                        + "not suffice for the zero-kernel equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-joint-quotient-well-defined"),
                DeclarationHandle.Create(Prefix + "weighted_joint_quotient_well_defined"),
                H("The distance is independent of representatives"),
                StatementSource.FromAuthor(WellDefinedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Changing either state without changing any selected readout leaves every "
                        + "term in the finite supremum unchanged. This descent needs no sign "
                        + "condition on the weights."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quotient-weighted-joint-distance"),
                DeclarationHandle.Create(Prefix + "quotientWeightedJointDistance"),
                H("Weighted distance descends to the observation quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quotient.liftOn2 applies the representative-invariance theorem to define "
                        + "a real-valued distance directly on two observation classes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-weighted-joint-zero-implies-equality"),
                DeclarationHandle.Create(
                    Prefix + "quotient_weighted_joint_zero_implies_eq"),
                H("Zero quotient distance implies equality"),
                StatementSource.FromAuthor(QuotientSeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positive weights turn zero representative distance into equality of the "
                        + "selected joint readouts, and Quotient.sound turns that kernel "
                        + "relation into equality of classes. No global MetricSpace instance "
                        + "is installed because this module records only descent and "
                        + "separation."))),
                DescribeRole.Theorem))));

    private static Formula WeightAt(Formula coordinate) =>
        Seq(F.Id("w"), Open, coordinate, Close);

    private static Formula ReadoutAt(Formula coordinate, Formula state) =>
        Seq(F.Id("q"), Open, coordinate, Comma, Sp, state, Close);

    private static Formula Selected(Formula state) =>
        Seq(new Formula.Subscript(F.Id("q"), F.Id("J")), Open, state, Close);

    private static Formula Distance(Formula first, Formula second) =>
        Seq(
            new Formula.Subscript(F.Id("d"), F.Id("J")),
            Open, first, Comma, Sp, second, Close);

    private static Formula QuotientDistance(Formula first, Formula second) =>
        Seq(
            F.Id("d"), Underscore, Grp(F.Id("quot")),
            Open, first, Comma, Sp, second, Close);

    private static Formula NonnegativeWeights() =>
        Seq(
            Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("J"), Comma, Sp,
            D(0), Sp, Leq, Sp, WeightAt(F.Id("i")));

    private static Formula PositiveWeights() =>
        Seq(
            Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("J"), Comma, Sp,
            D(0), Sp, Lt, Sp, WeightAt(F.Id("i")));

    private static Formula UltrametricFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        return Disp(Seq(
            NonnegativeWeights(), Sp, Rightarrow, RowBreak,
            Forall, Sp, x, Comma, Sp, y, Comma, Sp, z, Comma, Sp,
            Distance(x, z), Sp, Leq, Sp, Max, Open,
            Distance(x, y), Comma, Sp, Distance(y, z), Close, Dot));
    }

    private static Formula ZeroKernelFormula()
    {
        Formula i = F.Id("i");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula agreement = Seq(
            Forall, Sp, i, InMacro, Sp, F.Id("J"), Comma, Sp,
            ReadoutAt(i, x), Sp, Eq, Sp, ReadoutAt(i, y));
        return Disp(Seq(
            PositiveWeights(), Sp, Rightarrow, RowBreak,
            Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Distance(x, y), Sp, Eq, Sp, D(0), Sp, Iff, Sp, agreement, Dot));
    }

    private static Formula NegativeWeightFormula()
    {
        Formula i = F.Id("i");
        Formula first = F.Id("false");
        Formula middle = F.Id("true");
        Formula negative = Seq(
            Exists, Sp, i, InMacro, Sp, F.Id("J"), Comma, Sp,
            WeightAt(i), Sp, Lt, Sp, D(0));
        Formula triangle = Seq(
            Distance(first, first), Sp, Leq, Sp, Max, Open,
            Distance(first, middle), Comma, Sp, Distance(middle, first), Close);
        return Disp(Seq(negative, Sp, Land, Sp, Neg, Grp(triangle), Dot));
    }

    private static Formula ZeroWeightFormula()
    {
        Formula i = F.Id("i");
        Formula first = F.Id("false");
        Formula second = F.Id("true");
        return Disp(Seq(
            Exists, Sp, i, InMacro, Sp, F.Id("J"), Comma, Sp,
            WeightAt(i), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Distance(first, second), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            ReadoutAt(i, first), Sp, Neq, Sp, ReadoutAt(i, second), Dot));
    }

    private static Formula WellDefinedFormula()
    {
        Formula x = F.Id("x");
        Formula xPrime = Seq(x, Apos);
        Formula y = F.Id("y");
        Formula yPrime = Seq(y, Apos);
        Formula sameObservations = Seq(
            Selected(x), Sp, Eq, Sp, Selected(xPrime), Sp, Land, Sp,
            Selected(y), Sp, Eq, Sp, Selected(yPrime));
        return Disp(Seq(
            sameObservations, Sp, Rightarrow, RowBreak,
            Distance(x, y), Sp, Eq, Sp, Distance(xPrime, yPrime), Dot));
    }

    private static Formula QuotientSeparationFormula()
    {
        Formula first = F.Id("u");
        Formula second = F.Id("v");
        return Disp(Seq(
            PositiveWeights(), Sp, Rightarrow, RowBreak,
            QuotientDistance(first, second), Sp, Eq, Sp, D(0), Sp,
            Rightarrow, Sp, first, Sp, Eq, Sp, second, Dot));
    }
}
