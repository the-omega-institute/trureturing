using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteTreeObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/FiniteTreeObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common-terminal history amplification is incompatible with a strict all-time finite Bowen bound.",
        H("FiniteTreeObstruction"), Blocks(
        Describe.Lean(DescribeId.Create("amplification-contradiction"),
            DeclarationHandle.Create(Owner + "amplification_contradiction"),
            H("Common-terminal history contradiction"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For an actual metric carrier, a finite family of pairwise disjoint subsets whose " +
                "iterates stay strictly eta-close through a common terminal time and have the same " +
                "nonempty terminal image gives distinct points in one strict all-time Bowen set. " +
                "The proof includes time zero and uses terminal equality for every later natural time. " +
                "This declaration is the reusable cardinal endpoint; it does not encode a tree, a " +
                "recurrence mechanism, or a fold.")))),
        Describe.Lean(DescribeId.Create("not-fpe-of-amplification"),
            DeclarationHandle.Create(Owner + "not_finitelyPositiveExpansive_of_amplification"),
            H("Amplification excludes finite positive expansivity"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "If a concrete carrier construction supplies an amplified common-terminal family " +
                "for every positive eta and every finite N, then its continuous selfmap cannot be " +
                "finitely positively expansive. The finite-tree realization, finite test arcs, " +
                "terminal covering component, regular-target crossing, and fold construction remain " +
                "separate obligations and are intentionally not assumed by this endpoint.")))))));
}
