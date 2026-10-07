using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class OrderedCoordinateHistoryInterpreterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered coordinate histories and staged interpretation.",
        H("Ordered coordinate histories and staged interpretation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-coordinate-history-interpreter"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/OrderedCoordinateHistoryInterpreter.interpret_mass"),
                H("The exact mathematical construction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Coordinates form a finite type I and each actual coordinate i has its own "
                        + "finite nonempty alphabet X(i). A history is an injective ordered sequence "
                        + "of actual coordinate identities with dependent results. Appending an "
                        + "unread coordinate has a unique inverse consisting of its parent, "
                        + "coordinate and letter. A full history determines the complete named "
                        + "assignment without renaming coordinates.")),
                    Paragraph(Text(
                        "A flow consists of nonnegative real node, selection and result masses. "
                        + "Its root mass is one; selection masses sum to the node mass, result "
                        + "masses sum to the selected flow, every result is bounded by the actual "
                        + "coordinate capacity times its selection mass, and each child node has its "
                        + "incoming result mass. Terminal projection sums node masses over every "
                        + "full ordering with the given named assignment.")),
                    Paragraph(Text(
                        "At positive nodes and selections, scheduler and result rows are the "
                        + "corresponding mass ratios. Null nodes use the uniform unread-coordinate "
                        + "scheduler and null selections use the uniform row of the actual dependent "
                        + "alphabet. The only capacity premise needed by this construction is that "
                        + "each capacity is at least the reciprocal alphabet size; the original "
                        + "upper bound of one and nonempty coordinate set remain valid "
                        + "specializations.")),
                    Paragraph(Text(
                        "Independent finite scheduling and result tables supply every row. The "
                        + "actual adaptive recursion reads the current entries at its realized "
                        + "previous history. Structural history-fiber identities and induction show "
                        + "that the resulting trace has exactly every prescribed node mass, "
                        + "including all null branches. Dependence of result rows and coordinate "
                        + "choice on the previous history is allowed; independence of innovations "
                        + "does not assert independence of output coordinates."))),
                DescribeRole.Theorem))));
}
