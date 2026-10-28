using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.JointTwistedPeriodicHistories;

internal sealed class TwistedJointPeriodicHistoriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/TwistedJointPeriodicHistories.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint twisted returns reduce to one signed gcd return in an arbitrary finite group.",
        H("Joint twisted periodic histories"),
        Blocks(
            Paragraph(Text(
                "For a GroupMat C and natural parameters d,a,b, JointTwistedPeriod records one actual "
                + "expanded history satisfying the h-twist at d*a and the g-twist at d*b. The coefficients "
                + "a.gcdA b and a.gcdB b are the signed Bezout coefficients for the natural gcd.")),
            Describe.Lean(
                DescribeId.Create("joint-twisted-period-definition"),
                DeclarationHandle.Create(Prefix + "JointTwistedPeriod"),
                H("The joint return carrier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The carrier retains the actual history and both shift equations, including all numbered "
                    + "parallel edges and the left group-coordinate action."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-twisted-compatibility"),
                DeclarationHandle.Create(Prefix + "joint_compatibility"),
                H("Joint returns force noncommutative compatibility"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A single actual history carrying both returns forces Commute h g and h^b=g^a by comparing "
                    + "the same signed-time coordinate in the two orders."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-twisted-gcd-return"),
                DeclarationHandle.Create(Prefix + "joint_to_gcd"),
                H("Two returns imply the signed gcd return"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Bezout signed recovery combines the two return equations into a return at time d with twist "
                    + "h^(a.gcdA b)*g^(a.gcdB b)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-twisted-gcd-equivalence"),
                DeclarationHandle.Create(Prefix + "jointGcdEquiv"),
                H("History-preserving gcd equivalence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Under commutation and the power relation, signed recovery reconstructs both original returns "
                    + "from the gcd return, yielding an equivalence of actual-history subtypes."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-twisted-cardinality"),
                DeclarationHandle.Create(Prefix + "jointTwistedPeriod_card"),
                H("Exact joint coefficient count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For positive d and compatible twists, the joint carrier has the existing diagonal conjugacy "
                    + "sum at the gcd time."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-twisted-cardinality-conjugacy-invariant"),
                DeclarationHandle.Create(Prefix + "jointTwistedPeriod_card_conjugacy_invariant"),
                H("Conjugacy-invariant joint coefficient count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The same joint carrier cardinality can be written with any conjugate representative of the "
                    + "signed gcd twist. Reindexing the finite group sum by left multiplication preserves the "
                    + "noncommutative conjugacy weight."))), DescribeRole.Theorem))));
}
