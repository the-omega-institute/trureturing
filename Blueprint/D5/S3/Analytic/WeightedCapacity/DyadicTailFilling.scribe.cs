using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WeightedCapacity;

internal sealed class DyadicTailFillingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic Capacity Level Closures.",
        H("Dyadic Capacity Level Closures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dyadictailfilling-closure-level-eq-sublevel"),
                DeclarationHandle.Create("D5/S3/Analytic/WeightedCapacity/DyadicTailFilling.closure_level_eq_sublevel"),
                H("Closure of a finite-state dyadic level"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let each natural coordinate have an arbitrary finite natural capacity and weight "
                    + "two to the negative coordinate index. If the total weighted capacity is infinite, "
                    + "the closure of the finite-support states with any prescribed nonnegative dyadic "
                    + "sum is exactly the set of all bounded states whose extended sum is at most that "
                    + "value. In the finite-support carrier, the relative closure is the real readout "
                    + "sublevel. The product topology has discrete coordinate factors. The construction "
                    + "preserves any prescribed finite set of coordinates and fills the remaining "
                    + "deficit at the first capacity crossing; zero capacity gaps require no restriction."))),
                DescribeRole.Theorem))));
}
