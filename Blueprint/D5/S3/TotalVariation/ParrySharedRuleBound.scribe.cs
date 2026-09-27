using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParrySharedRuleBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One shared longest-zero-run rule has a stationary defect bounded uniformly over the Parry sources.",
        H("Uniform stationary defect of the shared rule"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shared-rule-bound"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/ParrySharedRuleBound.parry_shared_rule_bound"),
                H("The full finite-window bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every forbidden one-run length k at least two and every window "
                        + "length R at least one, the stationary defect of sharedRule R is at "
                        + "most the minimum of one and 512 divided by R. The table sharedRule "
                        + "does not depend on k. It selects a longest complete zero run, "
                        + "prefers the latest closing endpoint on ties, and transports strictly "
                        + "after that closing one. The defect is summed over every actual "
                        + "stationary signed state prefix with R plus one transitions.")),
                    Paragraph(Text(
                        "For R at least eighteen, write t for the natural number R minus two "
                        + "and n for the natural quotient of t by sixteen. The sharper bound "
                        + "is four divided by n, plus twice the exponential of minus t "
                        + "divided by sixteen, plus the power of 31/32 with natural exponent "
                        + "the quotient of R by four. These are finite-window estimates; "
                        + "all natural quotients are retained before conversion to real numbers.")),
                    Paragraph(Text(
                        "Let p be the actual Parry parameter and q equal one minus p. "
                        + "The root equation gives one half less than p, p at most two thirds, "
                        + "and q squared equal to p squared times one minus the power of p "
                        + "with exponent k minus one. For a code list of n pairs (z,w), require "
                        + "z at least one and w between one and k minus one. Its span is the "
                        + "sum of z plus w, and its weight is p raised to that span. Let C "
                        + "contain every such list with span at most t. Let S be its total "
                        + "weight, and M the weight of its lists whose first zero run is at "
                        + "least every zero run, counting ties.")),
                    Paragraph(Text(
                        "Truncate every zero-run length at B. Encoding tuples by their lists "
                        + "is injective, so the finite product-sum identity gives total weight "
                        + "equal to the nth power of the quantity one minus the Bth power of p. At the "
                        + "exponential tilt 6/5, the zero-run moment and the truncated one-run "
                        + "moment are each at most two. Thus the tilted code sum is at most "
                        + "four to the nth power. For every B at least t the fitting family "
                        + "is exactly C. Comparing the tilted weight on spans greater than t "
                        + "and letting B increase proves that one minus S is at most the "
                        + "exponential of minus t divided by sixteen.")),
                    Paragraph(Text(
                        "To bound M, first enlarge C to all truncated codes. Partition by "
                        + "the first zero-run length z. Summing the competitors constrained "
                        + "to lengths at most z gives the power of the quantity one minus the zth "
                        + "power of p, with exponent n minus one. The one-run factors normalize "
                        + "exactly. Bernoulli's inequality applied to consecutive values of "
                        + "one minus the (j plus one)th power of p bounds the tied-maximum "
                        + "summand by a consecutive difference of nth powers. The finite "
                        + "sum telescopes, giving M at most the reciprocal of the product p times n, hence "
                        + "at most two divided by n.")),
                    Paragraph(Text(
                        "The overlapping-window inclusion places each defect in one of "
                        + "three events: the old selected run opens at the exiting boundary, "
                        + "the new selected run closes at the entering boundary, or the new "
                        + "window has no complete run. Summing the actual path law uses "
                        + "transition row normalization for the old marginal and stationarity "
                        + "for the new marginal. Each selected-boundary mass is bounded by "
                        + "its actual two-bit cylinder mass times one minus S plus M. Both "
                        + "cylinder masses are at most one. The empty event contributes at "
                        + "most the power of 31/32 with exponent the natural quotient R/4. "
                        + "Their sum gives the refined estimate without an independence "
                        + "premise or conditioning on the fit event.")),
                    Paragraph(Text(
                        "For R at least eighteen, n is at least t divided by thirty-two. "
                        + "The first two terms are at most 160 divided by t. The empty-event "
                        + "term is at most the exponential of minus R divided by 256, hence "
                        + "at most 256 divided by R. Since 160 divided by the quantity R minus two is "
                        + "at most 180 divided by R, their sum is at most 436 divided by R "
                        + "and therefore at most 512 divided by R. For the remaining window "
                        + "lengths, normalization of the actual stationary prefix law bounds "
                        + "the defect by one and completes the minimum bound."))),
                DescribeRole.Theorem))));
}
