using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class PartialMenuFiniteHorizonDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DecisionValue/PartialMenuFiniteHorizonDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fiberwise partial menus preserve finite-horizon values, tied legal actions, and tagged prefix traces.",
        H("Finite-Horizon Descent for Partial Menus"),
        Blocks(
            Paragraph(Text(
                "A partial menu model assigns each state a finite nonempty set of named legal actions. "
                    + "The model also records a successor, real reward and terminal value, successful "
                    + "outputs and costs, and a tagged failure report with its failure cost. An action "
                    + "outside the menu takes the failure branch; it is never silently added to the menu.")),
            Describe.Lean(
                DescribeId.Create("partial-menu-finite-horizon-descent"),
                DeclarationHandle.Create(Prefix + "partial_menu_finite_horizon_descent"),
                H("Partial-menu value, action, and prefix descent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two models are related by an abstraction. Their legal menus agree on every "
                            + "abstract fiber. Legal successors, rewards, terminal values, successful "
                            + "outputs and costs, and illegal failure reports and costs all factor through "
                            + "that abstraction.")),
                    Paragraph(Text(
                        "Induction on the remaining horizon compares the finite maxima over the same "
                            + "legal labels. It gives equal Bellman values and exactly the same set of "
                            + "all tied optimal legal labels. A second induction on an arbitrary named "
                            + "action prefix compares the tagged execution records: successful outputs, "
                            + "total cost, failure reports, and the final abstract state agree. An illegal "
                            + "label remains a failure in both runs."))),
                DescribeRole.Theorem))));
}
