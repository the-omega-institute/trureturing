using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class OrderedGroupChainHistoriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.";
    private static Formula Id(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, Open, a, Close, Sp, Implies, Sp, Open, b, Close, Close);
    private static Formula And(Formula a, Formula b) => Seq(Open, Open, a, Close, Sp, Land, Sp, Open, b, Close, Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Product(Formula a, Formula b) => Call("Prod", a, b);
    private static Formula Inv(Formula a) => new Formula.Power(a, Seq(Minus, D(1)));
    private static Formula Path(string a) => Call("Path", Id(a));
    private static Formula History(string a) => Call("History", Call("expandedGraph", Id(a)));
    private static Formula EdgeAt(Formula x, Formula i) => Call("edgeAt", x, i);
    private static Formula Label(Formula e) => Call("label", e);
    private static Formula First(Formula p) => Call("first", p);
    private static Formula Second(Formula p) => Call("second", p);
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula GammaAt(Formula x) => Call("chainGamma", Id("c"), x);
    private static Formula Base => Call("chainBaseEquiv", Id("c"));
    private static Formula Skew => Call("chainSkewHomeomorph", Id("c"));
    private static Formula Expanded => Call("chainHistoryHomeomorph", Id("c"));
    private static Formula Length => Call("IntOfNat", Id("L"));
    private static Formula Shift(string a, Formula x) => Call("shift", Id(a), x);
    private static Formula Group(Formula body, bool finite = false, bool ordered = false,
        bool topology = false, bool discrete = false) => Q(body,
        [B("H", Id("Type")), B("group", Call("Group", Id("H"))),
         .. finite ? new[] { B("finite", Call("Fintype", Id("H"))) } : [],
         .. ordered ? new[] { B("order", Call("LinearOrder", Id("H"))) } : [],
         .. topology ? new[] { B("topology", Call("TopologicalSpace", Id("H"))),
             B(discrete ? "discrete" : "continuousGroup",
               Call(discrete ? "DiscreteTopology" : "IsTopologicalGroup", Id("H"))) } : []]);
    private static Formula Matrix(Formula body, bool topology = false,
        params Formula.BoundVariable[] extra) => Group(Q(body,
            [B("n", Id("Nat")), B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
             .. extra]), topology: topology);
    private static Formula Local(Formula body, bool topology = false,
        params Formula.BoundVariable[] extra) => Group(Q(body,
            [B("n", Id("Nat")), B("m", Id("Nat")),
             B("U", Call("GroupMat", Id("H"), Id("n"), Id("m"))),
             B("V", Call("GroupMat", Id("H"), Id("m"), Id("n"))), .. extra]),
            finite: true, ordered: true, topology: topology, discrete: true);
    private static Formula Chain(Formula body, bool topology = true,
        params Formula.BoundVariable[] extra) => Group(Q(body,
            [B("n", Id("Nat")), B("m", Id("Nat")), B("L", Id("Nat")),
             B("A", Call("GroupMat", Id("H"), Id("n"), Id("n"))),
             B("B", Call("GroupMat", Id("H"), Id("m"), Id("m"))),
             B("c", Call("Chain", Id("H"), Id("A"), Id("B"), Id("L"))), .. extra]),
            finite: true, ordered: true, topology: topology, discrete: true);
    private static DocumentBlock Item(string name, string title, Formula statement,
        string text, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create("ordered-history-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula Signed(string list, Formula t) =>
        Multiply(Id("k"), Call("ListProd", Call(list, Id("x"), t)));
    private static Formula Coordinate(Formula t) => Call("anchoredCoordinate", Id("x"), Id("k"), t);
    private static Formula Agree(Formula lo, Formula hi, string x, string y) =>
        Q(Imp(And(Seq(lo, Sp, Leq, Sp, Id("t")), Seq(Id("t"), Sp, Leq, Sp, hi)),
            Equal(EdgeAt(Id(x), Id("t")), EdgeAt(Id(y), Id("t")))), B("t", Id("Int")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed anchors identify every expanded history with a numbered base path and one group coordinate. Ordered overlap steps compose at the original time with exact asymmetric windows.",
        H("Ordered group chain histories"), Blocks(
            Paragraph(Text("An edge retains its source, target, group label and copy number. All finite matrix dimensions, zero coefficient fibers and zero chain lengths are allowed. The finite group order fixes each local increasing rank. The sufficient local identities do not require an inhabited vertex set or an essentiality premise.")),
            Paragraph(Text("An indexed chain has d(j) for j in Fin(L+1), square matrices A(j) at dimension d(j), and rectangular U(j), V(j) for j in Fin(L), with A(j)=U(j)V(j) and A(j+1)=V(j)U(j). Its recursive Chain is toChain of that same indexed data; the endpoint matrices are A(0) and A(L). Thus every chain formula below applies to these actual supplied factors, including essential chains.")),
            Item("positiveLabels", "Increasing positive labels",
                Matrix(Q(Equal(Call("positiveLabels", Id("x"), Add(Id("t"), D(1))),
                    Call("Append", Call("positiveLabels", Id("x"), Id("t")),
                        Call("Singleton", Label(EdgeAt(Id("x"), Call("IntOfNat", Id("t"))))))),
                    B("x", Path("A")), B("t", Id("Nat")))),
                "The zero list is empty. Appending the current label preserves the temporal order.", DescribeRole.Definition),
            Item("negativeLabels", "Descending inverse labels",
                Matrix(Q(Equal(Call("negativeLabels", Id("x"), Add(Id("t"), D(1))),
                    Call("Append", Call("negativeLabels", Id("x"), Id("t")),
                        Call("Singleton", Inv(Label(EdgeAt(Id("x"),
                            Seq(Minus, Call("IntOfNat", Add(Id("t"), D(1)))))))))),
                    B("x", Path("A")), B("t", Id("Nat")))),
                "At zero the list is empty. Its successive entries are a(-1) inverse, a(-2) inverse and so on, in descending time order.", DescribeRole.Definition),
            Item("anchoredCoordinate", "All signed coordinates from one anchor",
                Matrix(Q(Seq(Coordinate(Id("t")), Colon, Id("H")),
                    B("x", Path("A")), B("k", Id("H")), B("t", Id("Int")))),
                "Every integer is either Int.ofNat(s) or Int.negSucc(s), for s:Nat. The first coordinate is k times ListProd(positiveLabels(x,s)); the second is k times ListProd(negativeLabels(x,s+1)). Positive labels keep increasing time order, negative inverse labels keep descending time order, and the coordinate at zero is k.", DescribeRole.Definition),
            Item("anchored_seam", "The signed one-step recurrence",
                Matrix(Equal(Multiply(Coordinate(Id("t")), Label(EdgeAt(Id("x"), Id("t")))),
                    Coordinate(Add(Id("t"), D(1)))), false,
                    B("x", Path("A")), B("k", Id("H")), B("t", Id("Int"))),
                "The recurrence holds at every integer, including the seam from minus one to zero."),
            Item("anchored_unique", "Uniqueness on both signed tails",
                Matrix(Imp(And(Equal(Call("g", D(0)), Id("k")),
                    Q(Equal(Multiply(Call("g", Id("t")), Label(EdgeAt(Id("x"), Id("t")))),
                        Call("g", Add(Id("t"), D(1)))), B("t", Id("Int")))),
                    Q(Equal(Call("g", Id("t")), Coordinate(Id("t"))), B("t", Id("Int")))), false,
                    B("x", Path("A")), B("k", Id("H")),
                    B("g", new Formula.TypeArrow(Id("Int"), Id("H")))),
                "Forward induction and inverse recurrence induction recover all coordinates. There is no period constraint."),
            Item("anchoredHomeomorph", "Unrestricted anchored homeomorphism",
                Matrix(Seq(Call("anchoredHomeomorph", Id("A")), Colon,
                    Call("Homeomorph", History("A"), Product(Path("A"), Id("H")))), true),
                "The forward map keeps the numbered base path and the group coordinate at zero. The inverse reconstructs both signed tails. Each coordinate uses finitely many input labels, giving continuity in the product topology.", DescribeRole.Definition),
            Item("anchored_time", "The positive original-time action",
                Matrix(Equal(Apply(Call("anchoredHomeomorph", Id("A")),
                    Call("historyShift", Call("expandedGraph", Id("A")), Id("z"))),
                    Call("step", Id("A"), Apply(Call("anchoredHomeomorph", Id("A")), Id("z")))),
                    true, B("z", History("A"))),
                "The base path shifts by one and the anchor multiplies on the right by the current edge label."),
            Item("ordered_forward_seam", "All forward seams",
                Local(Call("Seam", Call("countedExpansion", Multiply(Id("U"), Id("V"))),
                    Call("countedExpansion", Multiply(Id("V"), Id("U"))), Call("orderedForward", Id("U"), Id("V")))),
                "The forward edge joins the current V half with the next U half. Its coordinate crosses the current U half. Both output endpoints and group coordinates match."),
            Item("ordered_backward_seam", "All past-aligned inverse seams",
                Local(Call("Seam", Call("countedExpansion", Multiply(Id("V"), Id("U"))),
                    Call("countedExpansion", Multiply(Id("U"), Id("V"))), Call("orderedBackward", Id("U"), Id("V")))),
                "The inverse reads U from the preceding output, V from the central output, and uses the central group coordinate multiplied by the inverse U label."),
            Item("ordered_local_criterion", "Both center recoveries",
                Local(Call("LocalCriterion", Call("orderedOverlapInput", Id("U"), Id("V")))),
                "The two seams and both center recoveries hold on every actual three-edge word. The same ordered ranks recover all parallel-edge numbers."),
            Item("orderedHistoryHomeomorph", "The actual ordered overlap homeomorphism",
                Local(Seq(Call("orderedHistoryHomeomorph", Id("U"), Id("V")), Colon,
                    Call("Homeomorph", Call("History", Call("expandedGraph", Multiply(Id("U"), Id("V")))),
                        Call("History", Call("expandedGraph", Multiply(Id("V"), Id("U")))))), true),
                "Applying the two tables at radii (0,1) and (1,0) gives continuous inverse maps on all legal histories, including empty carriers.", DescribeRole.Definition),
            Item("chainTransfers", "The actual ordered layer transfers",
                Chain(Seq(Call("chainTransfers", Id("c"), Id("x")), Colon, Call("List", Id("H"))),
                    false, B("x", Path("A"))),
                "For a cons layer, first record the U label at position zero, then evaluate the remaining transfer list at the actual output path of that layer. A nil chain gives the empty list.", DescribeRole.Definition),
            Item("chainGamma", "Gamma as the ordered list product",
                Chain(Equal(GammaAt(Id("x")), Call("ListProd", Call("chainTransfers", Id("c"), Id("x")))),
                    false, B("x", Path("A"))),
                "The product is c0(x0) c1(x1) through the last layer in precisely this order. At length zero it is one.", DescribeRole.Definition),
            Item("chainHistoryHomeomorph", "Expanded ordered-chain homeomorphism",
                Chain(Seq(Expanded, Colon, Call("Homeomorph", History("A"), History("B")))),
                "Compose each original forward table in increasing layer order. The inverse composes the original past-aligned inverse tables in decreasing layer order. No swapped forward algorithm is substituted.", DescribeRole.Definition),
            Item("chainBaseHomeomorph", "The same base-path homeomorphism",
                Chain(Seq(Call("chainBaseHomeomorph", Id("c")), Colon, Call("Homeomorph", Path("A"), Path("B")))),
                "The base maps are obtained from the same prescribed overlap algorithms. Both directions are continuous.", DescribeRole.Definition),
            Item("chain_forward_formula", "Forward formula for the whole actual chain",
                Chain(Equal(Apply(Skew, Id("p")), Pair(Apply(Base, First(Id("p"))),
                    Multiply(Second(Id("p")), GammaAt(First(Id("p")))))), true,
                    B("p", Product(Path("A"), Id("H")))),
                "Each successive right multiplication follows the retained transfer list. Both composites are identities because each original step is inverted."),
            Item("chain_inverse_formula", "Inverse formula with the same Gamma",
                Chain(Equal(Apply(Call("symm", Skew), Id("p")),
                    Pair(Apply(Call("symm", Base), First(Id("p"))),
                        Multiply(Second(Id("p")), Inv(GammaAt(Apply(Call("symm", Base), First(Id("p")))))))),
                    true, B("p", Product(Path("B"), Id("H")))),
                "The inverse of the product reverses the factor order. Gamma is evaluated at the recovered base history."),
            Item("chain_anchored_formula", "Expanded and product algorithms agree",
                Chain(Equal(Apply(Call("anchoredHomeomorph", Id("B")), Apply(Expanded, Id("z"))),
                    Apply(Skew, Apply(Call("anchoredHomeomorph", Id("A")), Id("z")))), true,
                    B("z", History("A"))),
                "This identifies the two actual implementations on every signed history."),
            Item("chain_cocycle", "Exact noncommutative telescoping",
                Chain(Equal(Multiply(Label(EdgeAt(Id("x"), D(0))), GammaAt(Shift("A", Id("x")))),
                    Multiply(GammaAt(Id("x")), Label(EdgeAt(Apply(Call("chainBaseHomeomorph", Id("c")), Id("x")), D(0))))), true,
                    B("x", Path("A"))),
                "The local label equations cancel only adjacent intermediate labels. No commutativity, positivity or periodicity is used."),
            Item("chain_gamma_continuous", "Continuity of Gamma",
                Chain(Call("Continuous", Call("chainGamma", Id("c")))),
                "The ordered transfer function is continuous, as the group coordinate of the same continuous skew map at anchor one."),
            Item("chain_time", "Whole-chain original-time transport",
                Chain(Equal(Apply(Skew, Call("step", Id("A"), Id("p"))),
                    Call("step", Id("B"), Apply(Skew, Id("p")))), true,
                    B("p", Product(Path("A"), Id("H")))),
                "All layers commute with the positive single time step, so their composition does too."),
            Item("chain_group", "Whole-chain left equivariance",
                Chain(Equal(Apply(Skew, Call("translate", Id("h"), Id("p"))),
                    Call("translate", Id("h"), Apply(Skew, Id("p")))), true,
                    B("h", Id("H")), B("p", Product(Path("A"), Id("H")))),
                "Left multiplication commutes with the ordered right transfer."),
            Item("chain_history_time", "Expanded original-time transport",
                Chain(Equal(Apply(Expanded, Call("historyShift", Call("expandedGraph", Id("A")), Id("z"))),
                    Call("historyShift", Call("expandedGraph", Id("B")), Apply(Expanded, Id("z")))), true,
                    B("z", History("A"))),
                "The expanded map commutes with the same positive single-step shift."),
            Item("chain_history_group", "Both expanded left-action laws",
                Chain(And(
                    Q(Equal(Apply(Expanded, Call("groupHistory", Id("A"), Id("h"), Id("z"))),
                        Call("groupHistory", Id("B"), Id("h"), Apply(Expanded, Id("z")))), B("z", History("A"))),
                    Q(Equal(Apply(Call("symm", Expanded), Call("groupHistory", Id("B"), Id("h"), Id("w"))),
                        Call("groupHistory", Id("A"), Id("h"), Apply(Call("symm", Expanded), Id("w")))), B("w", History("B")))),
                    true, B("h", Id("H"))),
                "Both the forward map and its reverse-layer inverse preserve the left group action."),
            Item("chain_forward_window", "Forward expanded window",
                Chain(Imp(Agree(Id("i"), Add(Id("i"), Length), "z", "w"),
                    Equal(EdgeAt(Apply(Expanded, Id("z")), Id("i")), EdgeAt(Apply(Expanded, Id("w")), Id("i")))),
                    true, B("z", History("A")), B("w", History("A")), B("i", Id("Int"))),
                "Direct forward-algorithm induction gives [i,i+L] for every integer i."),
            Item("chain_inverse_window", "Inverse expanded window",
                Chain(Imp(Agree(Subtract(Id("i"), Length), Id("i"), "z", "w"),
                    Equal(EdgeAt(Apply(Call("symm", Expanded), Id("z")), Id("i")),
                        EdgeAt(Apply(Call("symm", Expanded), Id("w")), Id("i")))), true,
                    B("z", History("B")), B("w", History("B")), B("i", Id("Int"))),
                "Direct inverse-algorithm induction gives [i-L,i], with decreasing layer order."),
            Item("chain_gamma_window", "Exact initial window of Gamma",
                Chain(Imp(Agree(D(0), Subtract(Length, D(1)), "x", "y"),
                    Equal(GammaAt(Id("x")), GammaAt(Id("y")))), false,
                    B("x", Path("A")), B("y", Path("A"))),
                "The first transfer reads position zero. Transfer j reads only [0,j], so the union is [0,L-1]. At L=0 the interval is empty, the history map is the identity and Gamma is one."))));
}
