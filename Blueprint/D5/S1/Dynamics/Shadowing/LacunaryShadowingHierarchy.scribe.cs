using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class LacunaryShadowingHierarchyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive finite neighborhood-shadowing level", H("Every positive finite neighborhood-shadowing level"), Blocks(
        Paragraph(Text("Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, arXiv:2509.04312v1, Questions 5.1 and 5.2 ask which N admit neighborhood (N+1)-shadowing without neighborhood N-shadowing, for dynamical systems and for subshifts. The explicit X_(N+2) supplies every positive finite level.")),
        Describe.Lean(DescribeId.Create("lacunary-shift-bijective"), DeclarationHandle.Create(Owner + "lacunary_shift_bijective"), H("Invertibility of the two-sided shift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Translation by minus one is a legal inverse of translation by one."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lacunary-shadowing-hierarchy"), DeclarationHandle.Create(Owner + "lacunary_shadowing_hierarchy"), H("The full finite hierarchy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every natural N>=1, X_(N+2) is nonempty and compact, its shift is continuous and bijective, and it has neighborhood (N+1)-shadowing while neighborhood N-shadowing fails. NeighborhoodFiniteShadowing means: for each positive accuracy, one positive tolerance works for every infinite natural-time pseudo-orbit; one fixed nonempty finite set A has cardinality at most the specified bound and initial diameter below the accuracy, and the distance to its shifted image is below the accuracy at every time. The member providing the approximation may vary with time; the set does not. Taking N=2 gives the previously highlighted neighborhood three but not two case. No all-time image-diameter bound or coherent single tracer is asserted."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("meddaugh-stephens-2025-neighborhood-shadowing-hierarchy"), ResolutionKind.Proved)),
        Paragraph(Text("The lacunary progression construction and phase-cover argument are attributed to the supplied Pro proposal; Codex implemented the complete Lean proof. The inspected primary v1 poses both hierarchy questions. A bounded search found no exact prior answer, but the full text of Ellie Stephens, Local Variations of Shadowing, announced by Baylor on November 6, 2026, was unavailable. The announcement concerns neighborhood shadowing but does not state a hierarchy theorem. No exhaustive priority claim follows.")))));
}
