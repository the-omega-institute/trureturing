using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMSharedStaticPilotDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMSharedStaticPilotData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact actual contexts and shared local readouts for the original suffix",
        H("Exact actual contexts and shared local readouts for the original suffix"),
        Blocks(
            Paragraph(Text("The 2497 rows retain the actual depth-12 suffix of the original EJM certificate: 624 splits, 970 symmetry cuts and 903 bound leaves. Equal actual local partial assignments select one original row/action/lower readout, yielding 647 triangle and 425 singleton readouts for 28896 actual local uses. The data supplies no acceptance theorem. Each readout, all 32 projections at every bound leaf, every child update and every symmetry cut still require kernel checks. The root has a nonempty fixed prefix and does not establish the universal score bound.")),
            Node("triangles", "triangles", "Original triangle readouts", "Each readout retains its original row, coordinate and outcome action, complete actual local assignment and original lower value."),
            Node("singletons", "singletons", "Original singleton readouts", "The singleton family retains the same complete association data independently of triangle readouts."),
            Node("contexts", "contexts", "Every actual partial context", "All twenty actual coordinate values or unknowns are explicit for each reached row."),
            Node("levels", "levels", "Original descent levels", "Levels retain the original fuel and must decrease strictly on every checked child edge."),
            Node("nodes", "nodes", "Complete actual successor and symmetry rules", "A split names its original coordinate and all four actual children; a symmetry leaf retains the original action tag and pivot."),
            Node("leaf-index", "leafIndex", "Associate a bound row with its selection tuple", "This index selects data only and contributes no assignment or arithmetic proof."),
            Node("leaf-rows", "leafRows", "Enumerate the actual numerical bound leaves", "All 903 original bound leaves are retained for complete validation."),
            Node("triangle-selection", "triangleSelection", "Select all sixteen actual triangle projections", "Every selected readout is checked against the complete actual projected assignment."),
            Node("singleton-selection", "singletonSelection", "Select all sixteen actual singleton projections", "Every selected singleton readout is independently checked against its complete actual projection."),
            Node("rows", "rows", "Assemble exact annotated rows", "An annotated row combines its actual assignment, original level and complete rule."),
            Node("bound", "bound", "Check the original lower-value sum and all local associations", "The bound checker consumes all thirty-two selected readouts at the actual supplied partial context and retains the original 6987435 threshold."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
