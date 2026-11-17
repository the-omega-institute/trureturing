using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.DendriteObstruction;

internal sealed class DendriteObstructionAllDendroidDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/DendriteObstruction/AllDendroid.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No finite positive expansivity on standard dendroids.",
        H("DendriteObstruction - AllDendroid"), Blocks(
        Describe.Lean(DescribeId.Create("standard-small-coconnected-openings"),
            DeclarationHandle.Create(Owner + "smallCoconnectedOpenings"),
            H("The standard dendroid hypotheses imply small openings"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every compact metric StandardDendroid X, SmallCoconnectedOpenings X holds. StandardDendroid consists exactly of actual arcwise connectedness and hereditary unicoherence. Given any compact connected nontrivial H contained in X and delta>0, there is a compact connected Q contained in H with nonempty H minus Q of diameter strictly below delta.")),
                Paragraph(Text("StandardDendroid.subcontinuum gives the same standard structure on the actual compact subtype H, with its induced metric. Its joining arcs give actual interval paths. Apply compact_path_small_opening there and map the resulting continuum into X by the subtype inclusion. This inclusion is isometric, and H minus the image of Q is exactly the image of its subtype complement. No local connectedness, uniform arc continuity, smoothness, planarity or finite branching is assumed."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("finite-small-orbits"),
            DeclarationHandle.Create(Owner + "finite_small_orbits_of_standard_dendroid"),
            H("Exact finite small orbits on every standard dendroid"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let X be any nondegenerate compact metric standard dendroid and f any continuous self-map. For every real epsilon>0 and every natural m>=2 there exists a Finset F of exactly m points such that the diameter of f^[n] applied to F is strictly below epsilon for every natural n, including zero. The map need not be surjective, injective or a homeomorphism.")),
                Paragraph(Text("The static opening theorem supplies precisely the separate opening premise of finite_small_orbits_of_standard_dendroid_and_openings. The existing continuum-preserving minimal invariant set and compact-history argument then gives the conclusion with its original strict inequalities and all-time quantifiers. The static facts are classical inputs to this dynamical consequence; no novelty is asserted for the static lemmas."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("not-finitely-positive-expansive"),
            DeclarationHandle.Create(Owner + "not_finitelyPositiveExpansive_of_standard_dendroid"),
            H("No finite positive expansivity on standard dendroids"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every continuous self-map of every nondegenerate compact metric StandardDendroid fails FinitelyPositiveExpansive. The exact finite-small-orbit conclusion contradicts any uniform finite bound on a forward Bowen set. This follows from the existing equivalence between failure of finite positive expansivity and the strict finite-set conclusion."))), DescribeRole.Theorem))));
}
