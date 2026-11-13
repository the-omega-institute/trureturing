using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class DanskinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The compact convex envelope has a right directional derivative attained by an optimizer and dominating every optimizer derivative.",
        H("Danskin directional derivative of a compact envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compact-envelope-right-directional-derivative"),
                DeclarationHandle.Create("D5/S3/Analytic/Convexity/Danskin.hasRightDirDeriv_iSup"),
                H("An attaining maximal optimizer derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be any real inner product space, Z any nonempty compact topological space, "
                        + "and X an open convex subset of E. For jointly continuous f on X times Z, "
                        + "convex in its E argument, suppose each optimizer at x has a right directional "
                        + "derivative in direction v. The supremum value function has such a derivative d. "
                        + "One optimizer attains d, and every optimizer derivative is at most d. "
                        + "Completeness of E, separation axioms on Z and uniqueness of optimizers are not premises.")),
                    Paragraph(Text(
                        "This is a faithful extraction of Daniel Lyng's Danskin.hasRightDirDeriv_iSup "
                        + "from Econlib at immutable revision d7bd9477476cade1c6695c8891746048ceddc52f, "
                        + "Econlib/Math/Analysis/Danskin.lean. Its original proof and live support are retained; "
                        + "the project header, imports and module visibility syntax are adapted. "
                        + "The original copyright and complete Apache 2.0 license are retained in "
                        + "docs/reports/licenses/econlib-Danskin-LICENSE.txt. No Optlib source is retained. "
                        + "The provenance tag records repository integration, not mathematical novelty.")),
                    Paragraph(Text(
                        "For continuous real b and h on a nonempty compact subset K of an arbitrary "
                        + "topological space, use the compact subtype K as Z, E equal to the reals, "
                        + "X equal to the whole real line, x=0, v=1 and f(s,z)=b(z)+s*h(z). "
                        + "Joint continuity follows from continuity of b and h; the parameter fibers are affine. "
                        + "Their directional derivatives are h(z). Attainment and domination identify d "
                        + "with the maximum of h on the full argmax of b. Subtracting t*d from the increment "
                        + "gives a remainder little-o of t on the literal filter t tending to zero from above. "
                        + "Apply the same theorem to -b and -h and negate the output to obtain the minimum "
                        + "formula with the minimum of h on the full argmin of b. All optimizer ties remain. "
                        + "These are application correspondences, not additional named declarations or an "
                        + "independent proof, and add no metric or finite-domain premise.")),
                    Paragraph(Text(
                        "Retire this extraction when this repository's own resolved Mathlib pin contains "
                        + "an equivalent general declaration with the full telescope and attaining/dominating "
                        + "conclusion, and both generic compact-subtype affine applications compile to the "
                        + "literal right maximum and minimum little-o expansions with the stated premises. "
                        + "Upstream acceptance alone is not the retirement condition. "
                        + "Escape registration is unfinished under https://github.com/the-omega-institute/trureturing/issues/29945. Independent proof-shape, live-consumer and first-freeze admission remain separate obligations."))),
                DescribeRole.Theorem))));
}
