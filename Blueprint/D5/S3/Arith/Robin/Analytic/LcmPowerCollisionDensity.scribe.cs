using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerCollisionDensityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/fankobayashimolnar2025family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real collision parameters of the LCM power thresholds are dense above one.",
        H("Collision parameters in every open interval"),
        Blocks(Describe.Lean(
            DescribeId.Create("collision-parameters-dense"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity.collision_parameters_dense"),
            H("Density with arbitrarily large exponents"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For distinct natural primes p and q, real endpoints 1<alpha<beta, "
                    + "and every natural M, there are a real kappa strictly between alpha "
                    + "and beta and natural i,j both at least M and at least one such that "
                    + "lcmPowerF(kappa,p,i)=lcmPowerF(kappa,q,j). The function is exactly "
                    + "the existing function of Fan, Kobayashi and Molnar, Definition 4.2.")),
                Paragraph(Text(
                    "Order the two primes. The logarithmic ratio of their positive leading "
                    + "coefficients strictly increases in kappa. The logarithms of distinct "
                    + "primes have irrational ratio, and their differences with two natural "
                    + "indices remain dense after any prescribed index cutoff. Choose such "
                    + "a difference strictly inside the two endpoint coefficient ratios. "
                    + "The fixed-parameter scaled limits force opposite strict signs "
                    + "at alpha and beta for sufficiently large indices. Continuity in "
                    + "kappa and the strict intermediate value theorem give the equality.")),
                Paragraph(Text(
                    "This answers the real-parameter existence question in Section 8 and "
                    + "also yields collisions at arbitrarily large parameters. Countability "
                    + "and the integer-parameter conclusions are separate statements."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("fan-kobayashi-molnar-2026-collision-density"),
                ResolutionKind.Proved)))));
}
