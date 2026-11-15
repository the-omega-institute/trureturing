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
            T("columns_append", "Literal column shift", "For every state s, real mask m and i in Fin 4, the i-th column of append s m is the (i+1)-th column of s when i<3, and is m when i=3. This includes all three state blocks."),
            N("maskEquiv", "Exact binary masks", "The positional-base equivalence finFunctionFinEquiv, composed with finTwoEquiv at every row, identifies all Fin 8 masks with Fin 3 → Bool."),
            T("maskEquiv_apply", "Little-endian row bits", "For every m in Fin 8 and row r in Fin 3, maskEquiv m r is exactly Nat.testBit m.val r.val. All 24 entries are kernel checked."),
            N("symbol", "Present and absent symbols", "An absent Option mask is encoded by 8. A present mask is encoded by its inverse under maskEquiv and therefore has value less than 8, including the present empty mask 0."),
            N("paddedWindow", "Actual signed column coordinates", "For every actual word w of width n and real centre c, the five symbols encode the padded columns c+i−2 for i in Fin 5."),
            N("present", "Existing vertices", "A vertex exists in the five-column window exactly when its column symbol is less than 8. The real empty symbol 0 still has all three vertices."),
            N("selected", "Selected vertices", "A vertex is selected exactly when it exists and the corresponding row bit in its column symbol is set. An absent symbol never selects a vertex."),
            N("Local", "Boolean witness existence", "Each of the three middle-column vertices has a selected closed neighbour. Every selected middle vertex has an existing closed-neighbour witness whose selected closed neighbourhood contains only that vertex. Candidate witnesses and selected vertices exclude absent columns. Witnesses are existential propositions and are not path choices."),
            T("local_paddedWindow_iff", "Exact finite-window fidelity", "For every width n, word w and actual centre c, Local (paddedWindow w c) is equivalent to ColumnTest (decode w) c. Signed-coordinate transport preserves every existing selected vertex, Manhattan distance, witness existence and uniqueness, including both open ends."),
            T("validWord_iff_local", "Every real centre", "For every width n and word w, ValidWord w is equivalent to Local (paddedWindow w c) at every c in Fin n. This follows through the actual-grid column criterion."),
            N("acceptedWords", "Executable accepted words", "The finite family filters every numeric Fin n → Fin 8 word by the exact Local test at all padded real centres."),
            T("actualCount_eq_acceptedWords", "Actual subset cardinality", "For every width n, actualCount n equals the cardinality of acceptedWords n. The proof composes the actual subset-word equivalence with the pinned numeric mask equivalence and the all-width local fidelity theorem."),
            T("actualCount_one", "The original first coefficient", "The actual width-one minimal dominating subset count is exactly 2. The proof transports to all eight numeric masks and checks the actual local predicate; the two subsets are the middle singleton and the pair of ends."),
            N("accepts", "The executable finite predicate", "accepts is the Boolean decision of Local over the finite five-column vertex domain."),
            N("window", "Append a fifth symbol", "The four state columns followed by the supplied symbol form the tested window."),
            N("terminal", "Both open-end checks", "A terminal state must accept its four columns followed by 8, and must also accept its last three columns followed by 8,8. These check the final two real columns."),
            N("fullStep", "Backward transfer", "For every integer state vector v and full state s, fullStep v s sums v(append s m) over precisely the accepted real masks m. Each mask contributes once."),
            N("fullOrbit", "All-length backward orbit", "fullOrbit 0 is the full terminal vector and fullOrbit(k+1) is fullStep(fullOrbit k). This is defined independently of actualCount."),
            Paragraph(Text("The full transfer sums contributions from accepted mask words. The two terminal tests enforce the same open boundaries as the actual graph. The all-length counting correspondence and the total quotient then connect these local predicates to the actual subset series."))),
        []));

    private static DocumentBlock N(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Definition);
    private static DocumentBlock T(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bt-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
