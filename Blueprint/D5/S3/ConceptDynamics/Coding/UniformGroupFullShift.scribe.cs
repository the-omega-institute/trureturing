using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class UniformGroupFullShiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.";
    private static Formula Power(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula I(string s) => F.Id(s.Replace("_", ""));
    private static Formula.BoundVariable B(string s, Formula t) => new(FormulaIdentifier.Create(s), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] vs) =>
        vs.Length == 0 ? f : new Formula.BindMany(FormulaQuantifier.ForAll, [.. vs], f);
    private static Formula G(Formula f, params Formula.BoundVariable[] vs) => Q(Seq(
        OpenBracket, Call("Group", I("H")), CloseBracket,
        OpenBracket, Call("Fintype", I("H")), CloseBracket,
        OpenBracket, Call("LinearOrder", I("H")), CloseBracket,
        Q(f, vs)), B("H", I("Type")));
    private static Formula Context(Formula f, bool group = true, bool finite = true,
        bool ordered = true, bool topology = false) => Q(Seq(
        group ? Seq(OpenBracket, Call("Group", I("H")), CloseBracket) : Seq(),
        finite ? Seq(OpenBracket, Call("Fintype", I("H")), CloseBracket) : Seq(),
        ordered ? Seq(OpenBracket, Call("LinearOrder", I("H")), CloseBracket) : Seq(),
        topology ? Seq(OpenBracket, Call("TopologicalSpace", I("H")), CloseBracket) : Seq(),
        f), B("H", I("Type")));
    private static Formula FiniteOnly(Formula f) => Context(f, group: false, ordered: false);
    private static Formula GroupFiniteN(Formula f, params Formula.BoundVariable[] vs) =>
        Context(Q(f, [B("n", I("Nat")), B("b", I("Nat")), .. vs]), ordered: false);
    private static Formula SymbolN(Formula f, params Formula.BoundVariable[] vs) =>
        Context(Q(f, [B("n", I("Nat")), B("b", I("Nat")), .. vs]), group: false, finite: false, ordered: false);
    private static Formula GroupSymbolN(Formula f, params Formula.BoundVariable[] vs) =>
        Context(Q(f, [B("n", I("Nat")), B("b", I("Nat")), .. vs]), finite: false, ordered: false);
    private static Formula TopN(Formula f, params Formula.BoundVariable[] vs) =>
        N(Topology(Q(f, vs)));
    private static Formula N(Formula f, params Formula.BoundVariable[] vs) =>
        G(Q(f, [B("n", I("Nat")), B("b", I("Nat")), .. vs]));
    private static Formula D => Call("uniformEndpoint", I("n"), I("b"));
    private static Formula Hist => Call("History", Call("expandedGraph", D));
    private static Formula FS => Call("FullShift", I("H"), I("n"), I("b"));
    private static Formula Sym => Call("FullSymbol", I("H"), I("n"), I("b"));
    private static Formula Forward(Formula z) => Call("fullshiftForward", I("n"), I("b"), z);
    private static Formula Inverse(Formula x) => Call("fullshiftInverse", I("n"), I("b"), x);
    private static Formula Coeff(Formula m, Formula i, Formula j, Formula g) =>
        Call("coeff", Call("entry", m, i, j), g);
    private static Formula And(params Formula[] fs) => Seq(Open, Seq(fs.SelectMany((f, k) =>
        k == 0 ? new[] { Grp(f) } : new[] { Land, Sp, Grp(f) }).ToArray()), Close);
    private static Formula TopologyFor(Formula h, Formula f, bool topologicalGroup = true) => Seq(
        OpenBracket, Call("TopologicalSpace", h), CloseBracket,
        OpenBracket, Call("DiscreteTopology", h), CloseBracket,
        topologicalGroup ? Seq(OpenBracket, Call("IsTopologicalGroup", h), CloseBracket) : Seq(), f);
    private static Formula Topology(Formula f, bool topologicalGroup = true) => TopologyFor(I("H"), f, topologicalGroup);
    private static DocumentBlock Item(string name, string title, Formula f, string text,
        DescribeRole role = DescribeRole.Definition) => Describe.Lean(
        DescribeId.Create("uniform-" + (name == "FullShift" ? "full-sequence-space" : name.Replace(".", "-").Replace("_", "-").ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(Disp(f)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula ChainAll(Formula f, params Formula.BoundVariable[] vs) => G(Topology(Q(f,
        [B("n", I("Nat")), B("m", I("Nat")), B("b", I("Nat")), B("L", I("Nat")),
        B("A", Call("GroupMat", I("H"), I("n"), I("n"))),
        B("c", Call("Chain", I("H"), I("A"), Call("uniformEndpoint", I("m"), I("b")), I("L"))), .. vs])));
    private static Formula CF => Call("chainFullshiftHomeomorph", I("c"));
    private static Formula PartitionFacts => And(
        Q(Equal(Call("IntCast", Coeff(Call("partitionMatrix", I("n"), I("parts")), I("i"), I("j"), I("g"))),
            Coeff(Call("partitionSource", I("n"), I("parts")), I("i"), I("j"), I("g"))),
            B("i", Call("Fin", I("n"))), B("j", Call("Fin", I("n"))), B("g", I("H"))),
        Q(Seq(Num(0), Lt, Coeff(Call("partitionMatrix", I("n"), I("parts")), I("i"), I("j"), I("g"))),
            B("i", Call("Fin", I("n"))), B("j", Call("Fin", I("n"))), B("g", I("H"))),
        Call("Essential", Call("expandedGraph", Call("partitionMatrix", I("n"), I("parts")))));
    private static Formula PartitionAll(Formula f, params Formula.BoundVariable[] vs) => G(Q(f,
        [B("n", I("Nat")), B("L", I("Nat")), B("parts", Call("List", I("Nat"))), .. vs]));
    private static Formula TopPartitionAll(Formula f, params Formula.BoundVariable[] vs) =>
        PartitionAll(Topology(f), vs);

    private static Formula DiscreteChainAll(Formula f, params Formula.BoundVariable[] vs) => G(Topology(Q(f,
        [B("n", I("Nat")), B("m", I("Nat")), B("b", I("Nat")), B("L", I("Nat")),
        B("A", Call("GroupMat", I("H"), I("n"), I("n"))),
        B("c", Call("Chain", I("H"), I("A"), Call("uniformEndpoint", I("m"), I("b")), I("L"))), .. vs]), false));
    private static Formula PartitionDataAll(Formula f) => G(Q(f,
        B("n", I("Nat")), B("parts", Call("List", I("Nat")))));
    private static Formula SignedPartitionAll(Formula f) => Context(Q(f,
        B("n", I("Nat")), B("parts", Call("List", I("Nat")))), ordered: false);
    private static Formula DiscretePartitionAll(Formula f, params Formula.BoundVariable[] vs) =>
        PartitionAll(Topology(f, false), vs);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform natural group-ring matrix has numbered-edge coordinates on the entire bilateral full shift. The inverse recovers the full expanded edge from adjacent symbols. Partition endpoints retain their coefficients and the supplied original-time chain.",
        H("Uniform group endpoints and explicit full-shift coordinates"), Blocks(
        Item("uH", "The uniform group-ring element", FiniteOnly(Seq(Call("uH", I("H")), Colon,
            Call("MonoidAlgebra", I("Nat"), I("H")))),
            "uH is the sum of single(h,1) over every h in the finite group H. The order on H fixes the earlier chain ranks; multiplication need not commute."),
        Item("uH_coeff", "Every uniform coefficient is one", G(Equal(Call("coeff", Call("uH", I("H")), I("g")), Num(1)), B("g", I("H"))),
            "For every group element g, the coefficient of g in uH is exactly one.", DescribeRole.Theorem),
        Item("uniformEndpoint", "The literal uniform endpoint", GroupFiniteN(Seq(D, Colon, Call("GroupMat", I("H"), I("n"), I("n")))),
            "D[i,j]=b times uH for every i,j in Fin n. This is exactly b J_n u_H, with J_n the all-one matrix. The coordinate construction also covers zero dimensions or zero copy count; the source proposition uses n,b at least one."),
        Item("uniformEndpoint_coeff", "The actual copy count", N(Equal(Coeff(D, I("i"), I("j"), I("g")), I("b")),
            B("i", Call("Fin", I("n"))), B("j", Call("Fin", I("n"))), B("g", I("H"))),
            "Every vertex pair and every group label has precisely b numbered parallel edges.", DescribeRole.Theorem),
        Item("numberEquiv", "Preserve the original copy number", N(Seq(Call("numberEquiv", I("n"), I("b"), I("i"), I("j"), I("g")), Colon,
            Call("Equiv", Call("Fin", Coeff(D, I("i"), I("j"), I("g"))), Call("Fin", I("b")))),
            B("i", Call("Fin", I("n"))), B("j", Call("Fin", I("n"))), B("g", I("H"))),
            "Use the increasing Fin cast supplied by uniformEndpoint_coeff. Its forward and inverse preserve the natural value of each original edge number."),
        Item("FullSymbol", "The full alphabet", SymbolN(Equal(Sym, Call("Product", Call("Fin", I("n")), Call("Product", I("H"), Call("Fin", I("b")))))),
            "A symbol is (source vertex, group coordinate, original copy number). Its cardinality is n times |H| times b."),
        Item("FullShift", "All bilateral symbol sequences", SymbolN(Equal(FS, Call("Function", I("Int"), Sym))),
            "The domain is every function from the integers to the alphabet, with the product topology. There is no legality restriction on adjacent symbols."),
        Item("fullShift", "The original positive one-step shift", SymbolN(Equal(Call("fullShift", I("x"), I("i")), Call("x", Add(I("i"), Num(1)))),
            B("x", FS), B("i", I("Int"))), "Shift reads x(i+1) at i."),
        Item("fullGroupAction", "The left group action", GroupSymbolN(Equal(Call("fullGroupAction", I("h"), I("x"), I("i")),
            Call("tuple", Call("source", Call("x", I("i"))), Multiply(I("h"), Call("group", Call("x", I("i")))), Call("copy", Call("x", I("i"))))),
            B("h", I("H")), B("x", FS), B("i", I("Int"))),
            "Left multiplication changes only the group coordinate. Vertex and copy data remain the same."),
        Item("fullshiftForward", "Read the current expanded edge", N(Seq(Forward(I("z")), Colon, FS), B("z", Hist)),
            "At every integer i, an expanded edge (source,target,label,copy,k) maps to (source,k,copy). The copy is transported by numberEquiv at those exact endpoints and label."),
        Item("fullshiftInverse", "Recover the entire edge from adjacent symbols", N(Seq(Inverse(I("x")), Colon, Hist), B("x", FS)),
            "For x(i)=(s,k,c), x(i+1)=(t,kNext,cNext), return the numbered base edge (s,t,k inverse times kNext,numberEquiv inverse(c)) together with k. The seam is k times (k inverse times kNext)=kNext, with the target vertex t equal to the next source. Every full-shift sequence is admissible."),
        Item("fullshift_inverse_forward", "Every symbol sequence is recovered", N(Equal(Forward(Inverse(I("x"))), I("x")), B("x", FS)),
            "The forward map after the inverse recovers all vertices, group coordinates and copies at all integer positions.", DescribeRole.Theorem),
        Item("fullshift_forward_inverse", "Every expanded history is recovered", N(Equal(Inverse(Forward(I("z"))), I("z")), B("z", Hist)),
            "The inverse after the forward map recovers the target by the history seam, the original label by group cancellation, and the actual dependent copy number by the increasing Fin cast roundtrip.", DescribeRole.Theorem),
        Item("fullshiftHomeomorph", "The actual full-shift homeomorphism", N(Topology(Seq(Call("fullshiftHomeomorph", I("n"), I("b")), Colon, Call("Homeomorph", Hist, FS)), false)),
            "For H with its discrete group topology, use the actual forward and inverse maps and the two proven identities. Forward continuity follows from the current coordinate; inverse continuity from i and i+1. No abelian or essentiality assumption is used to construct these maps."),
        Item("chain_fullshift_homeomorph", "Compose the same supplied chain", DiscreteChainAll(Seq(CF, Colon,
            Call("Homeomorph", Call("History", Call("expandedGraph", I("A"))), Call("FullShift", I("H"), I("m"), I("b"))))),
            "Compose chainHistoryHomeomorph(c) with fullshiftHomeomorph(m,b), in that order. The chain retains every actual natural group-ring factor and its original length L. The inverse composes in reverse order."),
        Item("CoordinateLaws", "Both actions and both exact window bounds", Context(Q(Seq(Call("CoordinateLaws", I("A"), I("m"), I("b"), I("L"), I("F")), Colon, I("Prop")),
            B("n", I("Nat")), B("m", I("Nat")), B("b", I("Nat")), B("L", I("Nat")), B("A", Call("GroupMat", I("H"), I("n"), I("n"))),
            B("F", Call("Homeomorph", Call("History", Call("expandedGraph", I("A"))), Call("FullShift", I("H"), I("m"), I("b"))))), finite: false, ordered: false, topology: true),
            "For a group H with a topology, CoordinateLaws asserts all six universal laws: F shift=shift F; F inverse shift=shift F inverse; F(hz)=hF(z); F inverse(hx)=hF inverse(x); equality of input expanded coordinates on [i,i+L] implies equality of the full output symbol at i; equality of input symbols on [i-L,i+1] implies equality of the full inverse expanded coordinate at i. All positions and both inputs are quantified. These are upper bounds, with no minimal-window claim."),
        Item("numberEquiv_roundtrip_heq", "Recover the original dependent copy number", N(
            Seq(Call("SameEndpointsAndLabel", I("i"), I("j"), I("g"), I("i2"), I("j2"), I("g2")), Implies,
                Call("HEq", Call("numberEquivInverse", I("n"), I("b"), I("i2"), I("j2"), I("g2"),
                    Call("numberEquiv", I("n"), I("b"), I("i"), I("j"), I("g"), I("x"))), I("x"))),
            B("i", Call("Fin", I("n"))), B("j", Call("Fin", I("n"))), B("g", I("H")),
            B("i2", Call("Fin", I("n"))), B("j2", Call("Fin", I("n"))), B("g2", I("H")),
            B("x", Call("Fin", Coeff(D, I("i"), I("j"), I("g"))))),
            "SameEndpointsAndLabel is the conjunction i=i2,j=j2,g=g2. With these exact equality proofs, the inverse increasing Fin cast at i2,j2,g2 after the forward cast at i,j,g recovers x heterogeneously. The actual history roundtrip consumes this law when recovering its target, label and dependent copy type.", DescribeRole.Theorem),
        Item("chain_fullshift_forward_window", "The whole forward symbol at its original chain window",
            ChainAll(Seq(Call("AgreeExpanded", I("z"), I("w"), I("i"), Add(I("i"), I("L"))), Implies,
                Equal(Call("value", Call("apply", CF, I("z")), I("i")), Call("value", Call("apply", CF, I("w")), I("i")))),
                B("z", Call("History", Call("expandedGraph", I("A")))), B("w", Call("History", Call("expandedGraph", I("A")))), B("i", I("Int"))),
            "AgreeExpanded means equality of the full expanded coordinates z(t)=w(t) at every integer t in [i,i+L]. It implies equality of the complete output symbol, including vertex, group coordinate and copy, at i. The endpoint forward map reads the current retained chain coordinate.", DescribeRole.Theorem),
        Item("chain_fullshift_inverse_window", "The whole inverse expanded coordinate at the combined window",
            ChainAll(Seq(Call("AgreeSymbols", I("z"), I("w"), Subtract(I("i"), I("L")), Add(I("i"), Num(1))), Implies,
                Equal(Call("value", Call("inverseApply", CF, I("z")), I("i")), Call("value", Call("inverseApply", CF, I("w")), I("i")))),
                B("z", Call("FullShift", I("H"), I("m"), I("b"))), B("w", Call("FullShift", I("H"), I("m"), I("b"))), B("i", I("Int"))),
            "AgreeSymbols is equality at every integer in [i-L,i+1]. Adjacent symbols recover each entire endpoint edge on [i-L,i], then the actual reversed composition of the supplied ordered chain recovers its full source coordinate at i. Source, target, group label, original copy and expanded group coordinate all occur in the equality.", DescribeRole.Theorem),
        Item("chain_fullshift_time", "The supplied chain preserves one-step original time",
            ChainAll(Equal(Call("apply", CF, Call("shift", I("z"))), Call("fullShift", Call("apply", CF, I("z")))), B("z", Call("History", Call("expandedGraph", I("A"))))),
            "For every source history, the actual chain-to-full-shift composition intertwines the positive one-step shifts. L is the original supplied chain length; time is not replaced by a power.", DescribeRole.Theorem),
        Item("chain_fullshift_group", "The supplied chain preserves every left group action",
            ChainAll(Equal(Call("apply", CF, Call("groupHistory", I("h"), I("z"))), Call("fullGroupAction", I("h"), Call("apply", CF, I("z")))), B("h", I("H")), B("z", Call("History", Call("expandedGraph", I("A"))))),
            "For every h and every source expanded history, the actual composition sends h acting on that history to h acting on its complete full-shift image. CoordinateLaws also derives the inverse time and inverse group identities from these equalities and the actual inverse homeomorphism.", DescribeRole.Theorem),
        Item("chain_coordinate_laws", "Both directions of the supplied-chain coordinates", ChainAll(
            Call("CoordinateLaws", I("A"), I("m"), I("b"), I("L"), CF)),
            "The actual homeomorphism for every supplied chain ending at b J_m u_H satisfies all six coordinate laws: original one-step time and left group action in both directions, forward [i,i+L] and inverse [i-L,i+1]. Its homeomorphism fields give both recovery identities and continuity. In the two-step C2 interpretation with m=b=2, the alphabet has eight symbols and these windows are [i,i+2] and [i-2,i+1]; applying this interpretation requires the actual literal factor identities and endpoint.", DescribeRole.Theorem),
        Item("positive_essential", "Positive diagonal identity coefficients give legal edges", G(Q(
            Call("Essential", Call("expandedGraph", I("A"))),
            B("n", I("Nat")), B("A", Call("GroupMat", I("H"), I("n"), I("n"))),
            B("hp", Q(Seq(Num(0), Lt, Coeff(I("A"), I("i"), I("i"), Num(1))), B("i", Call("Fin", I("n"))))))),
            "At each expanded vertex (i,k), an identity-labelled diagonal edge with copy zero supplies both an outgoing edge and an incoming edge. The assumption is on every diagonal identity coefficient; no global positivity or nonzero dimension is needed.", DescribeRole.Theorem),
        Item("jordanActive", "The literal Jordan superdiagonal predicate", Q(Seq(Call("jordanActive", I("parts"), I("i"), I("j")), Colon, I("Bool")),
            B("parts", Call("List", I("Nat"))), B("i", I("Nat")), B("j", I("Nat"))),
            "Process consecutive block sizes. In the current block, require j=i+1 and j below the block size; beyond it subtract that size from both indices and continue. Outside all blocks the predicate is false."),
        Item("jordanBlocks", "Independent block-diagonal Jordan entries", Q(Seq(Call("jordanBlocks", I("parts"), I("i"), I("j")), Colon, I("Nat")),
            B("parts", Call("List", I("Nat"))), B("i", I("Nat")), B("j", I("Nat"))),
            "This is diag(J_part1(0),J_part2(0),...). In a diagonal block return one exactly on its upper superdiagonal; off the diagonal blocks return zero; beyond the first block subtract its size and recurse. Padding outside the total size is zero. The coefficient correspondence uses the proven identity with jordanActive."),
        Item("partitionMatrix", "Natural coefficients of the original partition endpoint", PartitionDataAll(Seq(Call("partitionMatrix", I("n"), I("parts")), Colon,
            Call("GroupMat", I("H"), I("n"), I("n")))),
            "Let q=|H|, b=q cubed times n. An inactive Jordan entry has every coefficient b. An active entry has coefficient b+q(q-1) at the identity and b-q at each other group element. For q at least two and n at least one, all coefficients are strictly positive. For a partition of n, these entries use its actual consecutive Jordan blocks."),
        Item("partitionSource", "The signed source expression in the integer group ring", SignedPartitionAll(Seq(Call("partitionSource", I("n"), I("parts")), Colon,
            Call("Matrix", Call("Fin", I("n")), Call("Fin", I("n")), Call("MonoidAlgebra", I("Int"), I("H"))))),
            "The independent literal expression is q cubed n J_n u_H + q(q times 1_H-u_H) N_parts. N_parts is the actual block-diagonal matrix jordanBlocks. Each natural coefficient of partitionMatrix casts to the coefficient of this expression; positivity is derived from q at least two and n at least one, without an additional bound hypothesis."),
        Item("partitionFullShift", "The supplied partition-chain coordinates", DiscretePartitionAll(Seq(Call("partitionFullShift", I("parts"), I("c")), Colon,
            Call("Homeomorph", Call("History", Call("expandedGraph", Call("partitionMatrix", I("n"), I("parts")))), Call("FullShift", I("H"), I("n"), Multiply(Power(Call("card", I("H")), Num(3)), I("n"))))),
            B("c", Call("Chain", I("H"), Call("partitionMatrix", I("n"), I("parts")), Call("partitionMatrix", I("n"), Call("replicate", I("n"), Num(1))), I("L")))),
            "The only chain premise is an actual supplied chain from these original endpoints. The all-one partition has zero Jordan matrix, so its endpoint is literally uniform with b=q cubed n. The homeomorphism uses this identity rather than an endpoint-equality assumption."),
        Item("partition_coordinates", "All source partition endpoint obligations", TopPartitionAll(Seq(PartitionFacts, Land,
            Equal(Call("card", Call("FullSymbol", I("H"), I("n"), Multiply(Power(Call("card", I("H")), Num(3)), I("n")))), Multiply(Power(Call("card", I("H")), Num(4)), Power(I("n"), Num(2)))), Land,
            Call("CoordinateLaws", Call("partitionMatrix", I("n"), I("parts")), I("n"), Multiply(Power(Call("card", I("H")), Num(3)), I("n")), I("L"), Call("partitionFullShift", I("parts"), I("c")))),
            B("hn", Call("Positive", I("n"))), B("hq", Call("AtLeast", Call("card", I("H")), Num(2))),
            B("c", Call("Chain", I("H"), Call("partitionMatrix", I("n"), I("parts")), Call("partitionMatrix", I("n"), Call("replicate", I("n"), Num(1))), I("L")))),
            "The displayed coefficient cast, positivity and essentiality clauses quantify every original i,j,g. IntCast is the ordinary natural-to-integer coefficient map. The same theorem proves alphabet q to the fourth times n squared and all six CoordinateLaws for the supplied chain. Taking L=largestPart-1 gives forward [i,i+largestPart-1] and inverse [i-(largestPart-1),i+1]. This does not prove chain existence or a minimal window.", DescribeRole.Theorem))));
}
