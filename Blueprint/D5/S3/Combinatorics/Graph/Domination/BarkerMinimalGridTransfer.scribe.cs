using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class BarkerMinimalGridTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual labelled subsets, finite windows and all-length runs for the open three-row grid",
        H("Actual subsets and the all-length open-grid transfer"),
        Blocks(
            EN("MinimalDominating", "Inclusion minimality", "Domination uses SimpleGraph.IsDominating and is required separately. Every proper finite subset must fail domination. No minimum-cardinality, total-domination, independence or symmetry condition is added."),
            EN("Closed", "Closed neighbourhoods", "Closed G u v means u=v or G.Adj u v."),
            EN("ClosedPrivate", "Existential private witnesses", "ClosedPrivate G S v z means z is closed-adjacent to v and every selected closed neighbour of z equals v. Witnesses are propositions and are never counted choices."),
            ET("minimal_iff_closed_private", "Private-witness characterization", PrivateFormula(), "The proof applies TrapezohedralMinimalDomination.minimalDominating_iff_private and minimalDominating_iff_proper. Finite subsets and their underlying sets have the same domination predicate, and every subset of the finite vertex type has a finite-set representative. The isolated-or-outside-private-neighbour characterization, under the domination premise, is published as Proposition 1 of Gangloff and Talon, arXiv:1906.10779v2, https://arxiv.org/abs/1906.10779. No novelty is claimed for that characterization. No external prose or proof code is transplanted.",
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Automata/gangloff2019dominating"))),
            EN("grid", "The ordinary open grid", "Vertices are Fin 3 × Fin n; (r,c) represents the source label (r+1,c+1). Adjacency is exactly Nat.dist r s + Nat.dist c d = 1. The finite column type supplies open ends."),
            EN("encode", "Read the masks", "Each column mask has one Boolean bit for each of the three labelled rows. The bit is true exactly when the actual vertex belongs to the subset."),
            EN("decode", "Recover the subset", "The decoded subset contains precisely the vertices whose column-mask bit is true."),
            EN("mem_decode", "Selected bits", "For every width n, word w and vertex v, membership v ∈ decode w is equivalent to w(v.column)(v.row)=true.", DescribeRole.Theorem),
            EN("subsetWordEquiv", "One subset, one word", "Finset (Vertex n) and Word n are equivalent through mutually inverse encode and decode. No automorphisms or witness choices are identified."),
            EN("padded", "Real empty versus absent", "A signed column in 0 ≤ c < n returns some mask; other coordinates return none. The present all-false mask differs from absence."),
            EN("minimalSets", "The original family", "Filter every actual labelled vertex subset by MinimalDominating (grid n). The original family is defined before transport to words."),
            EN("actualCount", "The source count", "actualCount n is the cardinality of minimalSets n. The requested generating series uses positive n and separately sets its constant coefficient to zero."),
            EN("ValidWord", "Acceptance against the actual graph", "Acceptance means domination of decode w and an existential closed private witness for each selected vertex."),
            ET("validWord_iff", "Exact acceptance", ValidFormula(), "Apply the general characterization to the independently defined actual decoded subset."),
            EN("minimalWordEquiv", "Restrict the bijection", "Restrict subsetWordEquiv to the actual minimal dominating subsets and accepted words."),
            EN("ColumnTest", "Five-column criterion", "Every centre vertex is closed-dominated. Every selected centre vertex has an actual closed-neighbour witness; uniqueness is tested among selected vertices at column distance at most two. Actual finite-grid vertex types exclude absent witnesses."),
            ET("minimal_iff_column_tests", "Every real centre at every width", ColumnFormula(), "A witness is at column distance at most one, and every selected neighbour of it is at distance at most two by the natural-distance triangle inequality. This proves that the five-column restriction retains the complete proper-subset condition, including widths one and two."),
            Paragraph(Text("The actual subset family is the source of the count throughout the transfer construction. The column criterion supplies the local tests, and the subset-word equivalence preserves every labelled choice without counting existential witnesses.")),
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
            Paragraph(Text("The full transfer sums contributions from accepted mask words. The two terminal tests enforce the same open boundaries as the actual graph. The all-length counting correspondence and the total quotient then connect these local predicates to the actual subset series.")),
            PN("runWeight", "runWeight", "An appended-mask word receives the product of its accepted transition indicators and its full terminal weight. It is always zero or one.", DescribeRole.Definition),
            PN("sum_runWeight", "sum runWeight", "For every suffix length k and every full state s, summing runWeight k s over every Fin k → Fin 8 word is exactly fullOrbit k s. The first-mask function equivalence supplies the induction.", DescribeRole.Theorem),
            PN("expanded", "expanded", "Signed coordinates −2,−1,0,1 read the four history columns; the supplied suffix supplies successive real masks, and subsequent columns are absent.", DescribeRole.Definition),
            PN("expandedWindow", "expandedWindow", "The five symbols centred at a nonnegative coordinate are read from the history-and-suffix stream.", DescribeRole.Definition),
            PN("runWeight_iff_tests", "runWeight iff tests", "For every k, full state s and suffix w, runWeight k s w equals one exactly when every centre in Fin(k+2) satisfies the corresponding Local window test. The base k=0 is precisely the two terminal checks.", DescribeRole.Theorem),
            PN("start", "start", "The two labelled real masks a,b encode the full start state 8*a+b in the first block.", DescribeRole.Definition),
            PN("accepted_cons_iff", "accepted cons iff", "For every suffix length k, masks a,b and suffix w, the concatenated numeric word belongs to acceptedWords(k+2) exactly when its unique run from start a b has weight one.", DescribeRole.Theorem),
            PN("actualCount_fullOrbit", "actualCount fullOrbit", "For every natural k, the actual inclusion-minimal dominating subset count of the ordinary open grid of width k+2, cast to the integers, equals the sum of fullOrbit k over all 64 starts. This includes width two with no transitions.", DescribeRole.Theorem),
            Paragraph(Text("The generic CycleItalianDominationRecurrence.sum_pathWeight sums arbitrary intermediate states between fixed endpoints u and v for n+1 edges. At a positive suffix length k its parameters would be the state type Fin 4672, the unit admitted-edge matrix M, and n=k−1, followed by a terminal-weighted endpoint sum and a mask-word correspondence. The argument here defines each continuation by append and identifies its weight with the actual local tests for every k, including zero."))), []));

    private static DocumentBlock EN(string name, string title, string prose,
        DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create("bmg-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static DocumentBlock ET(string name, string title, Formula formula, string prose,
        AssessedProvenance? provenance = null) => Describe.Lean(
        DescribeId.Create("bmg-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula X(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula All(string v, Formula ty, Formula body) =>
        Seq(Forall, Sp, Par(Seq(X(v), Sp, Colon, Sp, ty)), Comma, Sp, body);
    private static Formula Ex(string v, Formula ty, Formula body) =>
        Seq(Exists, Sp, Par(Seq(X(v), Sp, Colon, Sp, ty)), Comma, Sp, body);
    private static Formula Rel(Formula l, FormulaRelationOperator op, Formula r) => new Formula.Relation(l, op, r);
    private static Formula Logic(Formula l, FormulaLogicOperator op, Formula r) => new Formula.Logic(Par(l), op, Par(r));
    private static Formula Iff(Formula l, Formula r) => Logic(l, FormulaLogicOperator.Iff, r);
    private static Formula And(Formula l, Formula r) => Logic(l, FormulaLogicOperator.And, r);
    private static Formula Imp(Formula l, Formula r) => Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula In(Formula l, Formula r) => Rel(l, FormulaRelationOperator.MemberOf, r);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Verts(Formula n) => Call("Vertex", n);
    private static Formula FS(Formula t) => Call("Finset", t);
    private static Formula PrivateFormula()
    {
        Formula v = X("V"), g = X("G"), s = X("S"), x = X("v"), z = X("z");
        Formula witnesses = All("v", v,
            Imp(In(x, s), Ex("z", v, Call("ClosedPrivate", g, s, x, z))));
        Formula characterization = Iff(Call("MinimalDominating", g, s),
            And(Call("IsDominating", g, s), witnesses));
        return All("V", X("Type"), Imp(Call("Finite", v),
            All("G", Call("SimpleGraph", v), All("S", FS(v), characterization))));
    }
    private static Formula ValidFormula()
    {
        Formula n = X("n"), w = X("w");
        return All("n", Nat, All("w", Call("Word", n), Iff(Call("ValidWord", w),
            Call("MinimalDominating", Call("grid", n), Call("decode", w)))));
    }
    private static Formula ColumnFormula()
    {
        Formula n = X("n"), s = X("S"), c = X("c");
        return All("n", Nat, All("S", FS(Verts(n)), Iff(Call("MinimalDominating", Call("grid", n), s),
            All("c", Call("Fin", n), Call("ColumnTest", s, c)))));
    }
    private static DocumentBlock N(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Definition);
    private static DocumentBlock T(string name, string title, string prose) => Node(name, title, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bt-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static DocumentBlock PN(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bp-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
