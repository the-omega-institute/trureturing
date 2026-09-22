using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class MixedAffineQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/MixedAffineQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded affine congruence systems descend exactly through a binary quotient with unchanged phases.",
        H("Phase-preserving mixed affine quotient"),
        Blocks(
            Paragraph(Text(
                "Fix a positive integer M and common period N equal to twice M. Each event has "
                    + "a fixed phase-compatibility guard and an arbitrary indexed family of rows "
                    + "e dividing a k plus b l minus c. Every modulus is positive and divides N. "
                    + "All coefficients and phases are unrestricted integers. The event and row "
                    + "index types may be empty, and zero normals are permitted.")),
            Describe.Lean(
                DescribeId.Create("activation"), DeclarationHandle.Create(Prefix + "carry"),
                H("Activation and binary carry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each original row put q equal to N divided by e, and F equal to q times "
                        + "the original affine expression. At the lift (k plus M u, l plus M v), "
                        + "the row requires M to divide F and requires F divided by M plus "
                        + "q times (a u plus b v) to be even. The original guard is also required. "
                        + "Activation of all rows need not imply consistency of these equations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("witness"), DeclarationHandle.Create(Prefix + "Witness"),
                H("Original-event witnesses for affine shapes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each nonempty binary shape has a prescribed anchor. Its witness requires "
                        + "the original guarded event at the anchor lift. For each binary point, "
                        + "the homogeneous rows q times the normal applied to its displacement "
                        + "from the anchor must be even exactly when the point belongs to the "
                        + "shape. These homogeneous tests depend on the coefficients and period, "
                        + "not on new phases. The full, line and point witnesses feed the six "
                        + "mixed-cover alternatives."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("projection"), DeclarationHandle.Create(Prefix + "ProjectedCriterion"),
                H("Conjunctions at a common representative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The projected criterion allows an integer representative (k plus M z, "
                        + "l plus M w). Every event selected by one minimal pattern is then "
                        + "tested at its prescribed offset from that same representative. "
                        + "Thus each alternative is a conjunction of original event predicates "
                        + "at shifted representatives, subject to fixed homogeneous shape tests. "
                        + "No phase variable is chosen by projection."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-descent"), DeclarationHandle.Create(Prefix + "result"),
                H("Exact mixed descent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem proves the carry equation for every integer lift and "
                            + "classifies every event slice as empty, full, line or point. A shape "
                            + "witness is equivalent to a nonempty shape being exactly that slice. "
                            + "For every integer basepoint, coverage of its four binary lifts is "
                            + "equivalent to the six-pattern criterion. That criterion is invariant "
                            + "under arbitrary integer multiples of M in both coordinates, and "
                            + "is equivalent to its projected form.")),
                    Paragraph(Text(
                        "Coverage of every integer pair, and coverage of the square from zero "
                            + "inclusive to N exclusive, are each equivalent to the criterion "
                            + "holding throughout the square from zero inclusive to M exclusive. "
                            + "All statements concern the same original row phases and guards. "
                            + "They assert no existence of a covering phase assignment.")),
                    Paragraph(Text(
                        "Three corners in an affine congruence system force the fourth, by "
                            + "the parallelogram identity for every row. Consequently a binary "
                            + "slice has zero, one, two or four points. Subtraction from an "
                            + "anchor row value and cancellation of M identify membership "
                            + "with the homogeneous binary equations. The mixed geometric "
                            + "identity then applies. Reducing integer lift coordinates modulo "
                            + "two and using Euclidean division proves both global equivalences. "
                            + "This direct congruence formulation makes no assertion about a "
                            + "projected lattice basis."))),
                DescribeRole.Theorem)),
        []));
}
