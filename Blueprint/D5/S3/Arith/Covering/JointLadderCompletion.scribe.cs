using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class JointLadderCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Several interfaces can jointly repair the complete hole left by deleting "
            + "a saturated prime chain. The repair uses fixed roots and genuinely "
            + "fresh numerical labels from the same original family.",
        H("Joint Fresh-Ladder Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-ladder-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Covering/JointLadderCompletion.joint_ladder_completion"),
                H("A joint root repair constructs a smaller whole cover"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be a whole cover with n pairwise distinct odd moduli "
                        + "greater than one. Let p and ell be distinct primes. "
                        + "Assume that the complete p-bearing inventory consists "
                        + "of p ell^j for zero through p minus one, with distinct "
                        + "actual first-p roots. The hole is the complement of all "
                        + "original classes whose moduli are not divisible by p.")),
                    Paragraph(Text(
                        "Take any finite indexed family of distinct odd integers "
                        + "s greater than one, each coprime to ell. At each s, "
                        + "choose a fixed finite set of roots modulo s. Its "
                        + "cardinality must be at most the number of heights j "
                        + "below p for which s ell^j is absent from the entire "
                        + "original numerical inventory. Assume that the sum of "
                        + "all chosen root counts is less than p, and that every "
                        + "point of the complete hole has its residue in at least "
                        + "one of the chosen root sets.")),
                    Paragraph(Text(
                        "Then there exists a whole cover by N pairwise distinct "
                        + "odd nonunit moduli with N less than n. No minimality "
                        + "hypothesis is needed for this construction. In "
                        + "particular, global class-count minimality rules out "
                        + "such a joint root repair.")),
                    Paragraph(Text(
                        "Inject the chosen roots at each s into its available "
                        + "heights. The existing residual theorem puts every "
                        + "hole point in the actual top-chain cofactor cylinder. "
                        + "For each assigned root and height, insert one fixed "
                        + "CRT class with that root and the top-chain cofactor "
                        + "phase. Retain every p-free original and delete the "
                        + "complete p-chain. The joint root-cover premise and "
                        + "the residual theorem prove coverage of every natural-number input.")),
                    Paragraph(Text(
                        "Distinct assigned heights prevent collisions within "
                        + "one ladder. Equality of labels from two ladders would, "
                        + "by coprimality with ell, make each base divide the "
                        + "other; injectivity of the base family identifies the "
                        + "ladder. Global freshness prevents collision with every "
                        + "retained original. Oddness and nonunitness hold for "
                        + "all inserted moduli. The new count is the retained "
                        + "count plus the sum of chosen root counts, hence "
                        + "strictly smaller than n.")),
                    Paragraph(Text(
                        "The bases need not be pairwise coprime, so interfaces "
                        + "such as 9 and 15 can share a separator. A chosen root "
                        + "set need not equal the entire hole projection: different "
                        + "ladders may repair different parts of the same hole. "
                        + "All choices are fixed for that one original F. The "
                        + "theorem does not supply these choices from separate "
                        + "marginal bounds, and does not assert that an improving "
                        + "joint repair always exists. The complete-chain "
                        + "exclusion and unrestricted noncoverage remain open."))),
                DescribeRole.Theorem))));
}
