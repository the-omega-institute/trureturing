using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class BarkerMinimalGridTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full open-grid frontier model has 4672 states, one Boolean witness-existence test per checked column, and two absent-column terminal checks.",
        H("The unpruned frontier model"),
        Blocks(
            N("columns", "All states", "State is Fin 4672. The first 64 states are (8,8,a,b), the next 512 are (8,a,b,c), and the final 4096 are (a,b,c,d), with real masks in lexicographic order. Real masks are 0 through 7; the absent symbol is 8."),
            N("append", "Append one real mask", "Append drops the first symbol, appends the supplied real mask, and encodes the resulting four columns in the next appropriate state block."),
            T("append_injective", "Distinct appended masks", "For every full state s, append s is injective on Fin 8. Thus distinct appended masks do not create edge multiplicity."),
            T("columns_append", "Literal column shift", "For every state s, real mask m and i in Fin 4, the i-th column of append s m is the (i+1)-th column of s when i<3, and is m when i=3. This includes all three state blocks."),
            N("present", "Existing vertices", "A vertex exists in the five-column window exactly when its column symbol is less than 8. The real empty symbol 0 still has all three vertices."),
            N("selected", "Selected vertices", "A vertex is selected exactly when it exists and the corresponding row bit in its column symbol is set. An absent symbol never selects a vertex."),
            N("Local", "Boolean witness existence", "Each of the three middle-column vertices has a selected closed neighbour. Every selected middle vertex has an existing closed-neighbour witness whose selected closed neighbourhood contains only that vertex. Candidate witnesses and selected vertices exclude absent columns. Witnesses are existential propositions and are not path choices."),
            N("accepts", "The executable finite predicate", "accepts is the Boolean decision of Local over the finite five-column vertex domain."),
            N("window", "Append a fifth symbol", "The four state columns followed by the supplied symbol form the tested window."),
            N("Edge", "Admitted directed edges", "An edge from s to t means that some real mask appends to t and the resulting five-column window is accepted."),
            N("transition", "Unit edge weights", "The integer matrix entry is 1 for an admitted edge and 0 otherwise."),
            N("initial", "All two-column starts", "The initial weight is 1 at all 64 states in the first block and 0 elsewhere. This includes every labelled pair of real masks, without symmetry reduction."),
            N("terminal", "Both open-end checks", "A terminal state must accept its four columns followed by 8, and must also accept its last three columns followed by 8,8. These check the final two real columns."),
            Paragraph(Text("The all-length bijection between actual accepted mask words and successful full-state paths remains unproved here. The identification of the Boolean Local predicate with the actual-grid ColumnTest, the separate width-one count, the full-state quotient certificate and the original generating-series endpoint also remain open formal interfaces. No actual-count or quotient equality is assumed."))),
        []));

    private static DocumentBlock N(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Definition);
    private static DocumentBlock T(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bt-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
