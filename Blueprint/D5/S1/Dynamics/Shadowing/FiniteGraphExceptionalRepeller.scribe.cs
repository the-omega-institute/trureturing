using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteGraphExceptionalRepellerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite invariant sets of transitive finitely positively expansive graph maps",
        H("Finite invariant sets of transitive finitely positively expansive graph maps"),
        Blocks(Describe.Lean(
            DescribeId.Create("transitive-graph-no-finite-missed-set"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/FiniteGraphExceptionalRepeller.finite_totally_invariant_eq_empty"),
            H("A proper finite totally invariant set is empty"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Suppose a nonempty finite totally invariant set exists. An iterate fixes the periodic incident arms and sends the other arms into them. Each periodic arm must move short distances away from its base point. An attracting arm would put an interval in a single forward Bowen ball. Choosing short neighborhoods along the arms gives a nonempty open set that backward iteration preserves and that misses another nonempty open set. This contradicts transitivity."))),
            DescribeRole.Theorem))));
}
