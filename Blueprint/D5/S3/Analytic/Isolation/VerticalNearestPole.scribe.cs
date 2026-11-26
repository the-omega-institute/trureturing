using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class VerticalNearestPoleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A small vertical displacement isolates a nearest spectral point.",
        H("Vertical isolation of a nearest point"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("isolated-nearest-vertical-perturbation"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/VerticalNearestPole."
                    + "isolated_nearest_of_vertical_perturbation"),
                H("An isolated nearest point after an arbitrarily small displacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose a complex spectrum is locally discrete in the "
                        + "positive half-plane and lies strictly to the left of a vertical "
                        + "line. Fix a radius smaller than the line's real coordinate, and "
                        + "a spectral point whose horizontal distance from the line is "
                        + "smaller than that radius. For any positive tolerance, one can "
                        + "move the center vertically by less than that tolerance and "
                        + "choose a disk of at most the fixed radius containing exactly "
                        + "one spectral point.")),
                    Paragraph(Text("Only finitely many spectral points can meet a slightly "
                        + "enlarged compact disk. Each distinct pair has at most one "
                        + "equidistant height on the line. Avoiding this finite set of "
                        + "heights makes the nearest point unique, and its distance is "
                        + "strictly smaller than the next distance and the allowed radius.")),
                    Paragraph(Text("This is a geometric selection theorem. It does not "
                        + "assert analytic continuation or pole residues."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-center-spectral-dichotomy"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/VerticalNearestPole."
                    + "real_center_spectral_dichotomy"),
                H("A free disk or an isolated real point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a positive threshold below the real coordinate "
                        + "of the center, and assume that some spectral point lies to "
                        + "the right of that threshold. Either a disk around the real "
                        + "center is free of spectral points while another point is "
                        + "horizontally closer than its radius, or the unique closest "
                        + "point is real and lies to the right of the threshold.")),
                    Paragraph(Text("In the second case a slightly larger disk contains "
                        + "only that real point. Both radii are bounded by the "
                        + "difference between the center and the threshold. The "
                        + "conclusion concerns locations only, with analytic and "
                        + "residue information left to the corresponding functions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regularized-positive-log-family"),
                DeclarationHandle.Create("D5/S3/Analytic/Isolation/VerticalNearestPole."
                    + "regularized_positive_log_family"),
                H("Regularization at one preserves nonzero actual zero poles"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the family members be entire and nonzero at one, with positive real "
                    + "weights. Subtract the affine normalization of their logarithmic "
                    + "derivative sum so that its numerator vanishes at one. Taking its analytic "
                    + "divided difference at one and dividing by the negative coordinate "
                    + "produces a continuation with the artificial pole at one removed. It is "
                    + "analytic at every nonzero point where all family members are nonzero. "
                    + "At a nonzero actual zero its residue is minus the weighted positive "
                    + "analytic "
                    + "multiplicity divided by the coordinate times its displacement from one, "
                    + "and its meromorphic order is exactly minus one."))),
                DescribeRole.Theorem))));
}
