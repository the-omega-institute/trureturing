using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class SymmetricScenesRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/SymmetricScenesRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/lundqvist2026symmetricscenes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected free C2 incidence geometry satisfies every literal source count "
            + "but has an algebraically generic nontrivial symmetric scene.",
        H("Symmetric scene lifting sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-scenes-original-lifting-sufficiency"),
                DeclarationHandle.Create(Prefix + "liftingSufficiency"),
                H("The complete source lifting assertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every d >= 2, finite connected labelled incidence geometry with "
                    + "degree at least d, finite group acting freely and faithfully on "
                    + "both point and hyperplane labels, orthogonal representation, "
                    + "sign character and actual representative gain chart, the full "
                    + "orbit-count equality and every incidence-orbit subset inequality "
                    + "imply minimal symmetric flatness of every generic symmetric picture. "
                    + "Genericity means algebraic independence over Q of all coordinates "
                    + "of point-orbit representatives. Component penalties are the finranks "
                    + "of the actual invariant hyperplane subspaces for unbounded closed "
                    + "gain walks. This is the lifting clause of Conjecture 6.1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-scenes-original-lifting-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A generic connected lifting counterexample"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The result proves Not OriginalSource.liftingSufficiency. Use d=3, "
                        + "C2 with tau=-I2 and the trivial character, three point orbits and "
                        + "two distinct hyperplane orbits. At each hyperplane label the gain "
                        + "incidences are (P0,0),(P0,1),(P1,0),(P2,0). The connected full cover "
                        + "has 6 points, 4 hyperplanes and 16 distinct incidences, a free "
                        + "faithful action, and degree 4 at every hyperplane.")),
                    Paragraph(Text(
                        "Every literal orbit subset, supported component, unbounded gain "
                        + "closure and genuine invariant-space dimension transports from "
                        + "the C2 witness to the general source telescope. The "
                        + "same representative coordinates are algebraically independent. "
                        + "The explicit scene uses positive-copy normal (-b,a), zero "
                        + "constants, and heights 0,-(ad-bc),-(af-be). Opposite-copy normals "
                        + "differ, so the scene is nonflat. No affine-spanning premise is used.")),
                    Paragraph(Text(
                        "Nonflatness contradicts the necessary flatness clause of minimal "
                        + "flatness. The parallel-redrawing clause and Conjecture 6.2 remain "
                        + "outside this conclusion."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "lundqvist-schulze-stokes-symmetric-scenes-lifting-refutation"),
                    ResolutionKind.Refuted)))));
}
