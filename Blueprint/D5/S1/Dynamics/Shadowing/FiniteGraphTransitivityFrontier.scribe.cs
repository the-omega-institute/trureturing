using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteGraphTransitivityFrontierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite sets missed by iterated arcs in transitive graphs",
        H("Finite sets missed by iterated arcs in transitive graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("transitive-graph-finite-missed-set"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/FiniteGraphTransitivityFrontier.exists_edgeChart_Icc_finite_exceptional_set"),
            H("The forward images of a free subarc miss a finite totally invariant set"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every nonempty open set in a nontrivial connected finite graph contains a closed free subarc. Transitivity supplies a positive return time for the arc. Images with indices in the same residue class form a connected union, and the closure of each such union adds only finitely many points. Their dense union therefore has a finite complement, which the map permutes and whose full preimage equals itself."))),
            DescribeRole.Theorem))));
}
