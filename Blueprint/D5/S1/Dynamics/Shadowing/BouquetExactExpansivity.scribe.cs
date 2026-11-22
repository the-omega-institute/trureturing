using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class BouquetExactExpansivityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/BouquetExactExpansivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Topologically exact maps on finite bouquets of circles",
        H("Topologically exact maps on finite bouquets of circles"),
        Blocks(
            Paragraph(Text("Identify the origins of N labelled circles to form a bouquet. Projection forgets the label. A traversal of the bouquet visits all circles consecutively, sending each junction of the traversal to the common vertex.")),
            Describe.Lean(
                DescribeId.Create("bouquet-whole-space-traversal"),
                DeclarationHandle.Create(Owner + "continuous_traverse"),
                H("The traversal descends continuously to the circle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any positive number of circles, concatenate the labelled circles at their common vertex. The finite closed quotient identifies the adjacent parameter endpoints and gives a continuous map from the circle onto the bouquet."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bouquet-topologically-exact-positive-expansivity"),
                DeclarationHandle.Create(Owner + "exact_order"),
                H("A topologically exact map of positive expansivity order N"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For N at least two, compose projection with traversal to obtain a continuous surjection of the compact bouquet. On the projected circle the map multiplies by N. The projection of any nonempty open set contains an arc, and a sufficiently large multiplication iterate maps the arc onto the circle. One more traversal covers the bouquet.")),
                    Paragraph(Text("At a sufficiently small scale each strict forward Bowen ball lies in a projection fiber of size at most N. Points on different circles approach the shared vertex at the same projected phase, stay distinct at time zero, and coalesce at time one. At every positive scale they witness failure of a bound by N minus one.")),
                    Paragraph(Text("Gangloff, Guillon and Oprocha's Remark 3.10 already realizes exact finite orders on bouquets. Its example of order greater than one maps into a proper subbouquet. The construction here adds surjectivity and topological exactness."))),
                DescribeRole.Theorem))));
}
