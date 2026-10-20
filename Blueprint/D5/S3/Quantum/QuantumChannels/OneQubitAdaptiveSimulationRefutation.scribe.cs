using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class OneQubitAdaptiveSimulationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/kotowski2026smallancilla");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A family of sign-frame channels has exact postselection success at most 4 times 4 to the R divided by n for every adaptive protocol with one ancillary qubit and at most R measurement rounds. Finite classical randomization preserves this bound, excluding universal constant depth and constant positive success.",
        H("One ancillary qubit cannot give constant-round universal channel simulation"),
        Blocks(
            Node("workspace", "Workspace", "The system and its ancillary qubit", WorkspaceFormula(),
                "For a system with coordinate type I, the joint workspace has coordinates I times Fin(2). Workspace is the complex square-matrix algebra with its operator norm. In the formulas, ofMatrix denotes CStarMatrix.ofMatrix, and symm(ofMatrix) is its inverse, taking a workspace operator to its ordinary matrix; adjoint denotes conjugate transpose. The finite-type and decidable-equality structures on I are assumed to exist.", true),
            Node("measurement", "Measurement", "A complete projective measurement", MeasurementFormula(),
                "A measurement consists of a family P of k workspace operators and a proof that their underlying matrices form a complete family of pairwise orthogonal self-adjoint projections. Zero projections are allowed. There is no bound on k. This is the projective-measurement operation allowed in Question 6.1 of Kotowski and Kotowski. The displayed dependent sum spells out the projector and record fields.", true),
            Node("protocol", "Protocol", "Adaptive protocol trees", ProtocolFormula(),
                "These are the constructors of an inductively generated family of finite trees, with no other constructors. A leaf records a Boolean success flag and is allowed at every depth bound R. A node applies U, measures P, and chooses the child indexed by the observed outcome. Its children have depth bound R and the node has depth bound R+1. The subscript on leaf records its implicit depth bound. This describes the unitary, measurement and adaptive operations of Question 6.1 with the ancilla initially in the fixed state zero.", true),
            Node("history", "History", "Complete measurement histories", HistoryFormula(),
                "A leaf has the single history of Unit. At a node, a history is an outcome o followed by a history of the child c(o). The dependent sum retains which continuation belongs to each observed outcome.", true),
            Node("history-fintype", "historyFintype", "The finite set of histories", HistoryFintypeFormula(),
                "Every tree has a finite history type: Unit is finite, and a finite dependent sum of finite child-history types is finite. The displayed term supplies that finite-type structure.", true),
            Node("succeeds", "succeeds", "Which histories succeed", SucceedsFormula(),
                "The success flag of a complete history is the flag on its terminal leaf. Both true and false leaves are permitted, independently at different histories.", true),
            Node("branch", "branch", "Ordered branch products", BranchFormula(),
                "The empty branch has operator one. At a node, the current unitary acts first, followed by the outcome projector and then the remaining branch product. Thus earlier operations occur on the right of the product.", true),
            Node("kraus-from", "krausFrom", "Compression to the system", KrausFormula(),
                "The prefix B is any workspace operator. On a successful history, compress branch(t,h) B from the input ancilla coordinate zero to the output ancilla coordinate a. A failed history contributes the zero matrix. The formula is entrywise for every pair of system coordinates; it imposes no norm condition on B. In the successful map B is one, so the input ancilla is fixed and summing over a discards the final qubit.", true),
            Node("tree-successful-map", "successfulMap", "The successful map of a tree", TreeMapFormula(),
                "For a deterministic tree t, sum the Kraus conjugations over every complete history and both final ancillary basis coordinates. Failed histories contribute zero. This is the unnormalized successful map; equality to q times a trace-preserving target channel gives input-independent success probability q, as in the postselection convention of Definition 2.3.", true),
            Node("randomized-protocol", "RandomizedProtocol", "Finite classical randomization", RandomizedFormula(),
                "The record has a natural number N of seeds, a real probability vector w in the standard simplex on Fin(N), and a tree c(s) of the same depth bound for each seed. The standard simplex requires nonnegative weights with sum one. The dependent sum selects N, and its body is the product of the probability and tree fields. This is the finite classical randomization allowed in the simulation model.", true),
            Node("randomized-successful-map", "mixtureMap", "The successful map after randomization", RandomizedMapFormula(),
                "For a randomized protocol p, average the successful maps of its trees with its real simplex weights, cast to complex scalars. Each input matrix uses the same distribution of trees.", true),
            Node("claim", "claim", "Universal depth and success constants", ClaimFormula(),
                "This is the affirmative reading of Question 6.1: there are a natural depth bound Rzero and a positive real qzero, both independent of dimension and target channel, such that every completely positive trace-preserving channel has an exact successful map q times that channel with q at least qzero. The displayed channel action first applies ofMatrix to X, then the channel's toCompletelyPositiveMap, and finally symm(ofMatrix). Equality is on every complex matrix, not only one input state. The source's Definition 2.3 supplies the postselection convention; Question 6.1 adds projective measurements and adaptive unitaries. The definition imposes qzero at most q and does not include a separate upper bound on q.", true),
            Node("frame-index", "FrameIndex", "Basis coordinates and sign coordinates", FrameIndexFormula(),
                "For m=n squared, the coordinate type is the disjoint sum of m basis labels and all Boolean strings of length m. Its cardinality is d=m+2 to the m. No positivity assumption on n is part of this type definition."),
            Node("frame", "frame", "The sign frame", FrameFormula(),
                "The basis rows form the identity matrix. A Boolean sign row has entry +1/n where the Boolean is true and -1/n where it is false. The displayed real conditional equals boolSign applied to the Boolean complement; ofReal embeds it into the complex numbers. The notation natCast(C,n) denotes the natural-to-complex embedding of the denominator. The definition includes n=0, where there are no column indices. For positive n every row has squared Euclidean norm one."),
            Node("frame-nat", "frameNat", "Relabelling the frame by a finite ordinal", FrameNatFormula(),
                "Relabel the rows of frame(n) by Fin(card(FrameIndex(n))) using the inverse of Fintype.equivFin; the column labels are unchanged. This puts the same frame on the coordinate type used by the universal channel claim."),
            Describe.Lean(
                DescribeId.Create("kk-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The universal constants do not exist"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The sign-frame family is a repository construction addressing the question of Kotowski and Kotowski. Fix an integer n at least 2, put m=n squared and d=m+2 to the m, and let A=frame(n). Relabel its rows by frameNat(n) when using Fin(d). With D_j the diagonal matrix formed from column j, define the channel Phi_n by the sum of D_j X D_j adjoint. The unit norm of every row makes this channel trace preserving and unital. In the displayed bound natCast(R,n) denotes the natural-to-real embedding.")),
                    new DocumentBlock.DisplayFormula(FrameChannelBoundFormula()),
                    Paragraph(Text("Suppose the successful map equals q Phi_n on every matrix. For every seed of positive probability, each successful compressed Kraus matrix is diagonal of the form diag(A v). Every nonzero such matrix has rank at least r=2 to the (m-1) plus 1. Since 5r>2d, a projective measurement on the joint 2d-dimensional workspace has at most four outcomes admitting a nonzero successful continuation. A deterministic tree of depth at most R therefore has at most 4 to the R useful histories and at most 2 times 4 to the R nonzero successful compressed Kraus matrices. This is a bound for each tree, irrespective of how many seeds occur in the finite randomization.")),
                    Paragraph(Text("Each of these compressed Kraus matrices is a contraction. The basis rows give |v_j| at most 1. Choosing sign rows separately for the real and imaginary parts gives sum_j |Re(v_j)| at most n and sum_j |Im(v_j)| at most n. Consequently sum_j |v_j| squared is at most 2n. The total coefficient energy of one tree is at most 4n times 4 to the R. Averaging over the seeds preserves this bound, while comparison on the basis-coordinate diagonal inputs gives total weighted coefficient energy q m. Hence q n is at most 4 times 4 to the R, or equivalently q is at most 4 times 4 to the R divided by n.")),
                    Paragraph(Text("Given any proposed Rzero and qzero>0, choose an integer n at least 2 and strictly greater than 4 times 4 to the Rzero divided by qzero. Applying the claim to Phi_n requires q at least qzero and contradicts the bound. The conclusion concerns exact simulation with one ancillary qubit, arbitrary finite projective measurements, finite classical randomization and adaptive trees with a dimension-independent round bound. It leaves protocols whose depth grows with dimension and protocols whose success decreases with dimension outside this obstruction."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kotowski-kotowski-2026-one-qubit-simulation-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title,
        Formula formula, string prose, bool literature = false) => Describe.Lean(
        DescribeId.Create("kk-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula NeTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula PlusTo(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula Product(Formula left, Formula right) =>
        Parenthesized(Seq(Parenthesized(left), Sp, Times, Sp, Parenthesized(right)));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Typed(Formula term, Formula type) => Seq(term, Sp, Colon, Sp, type);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Mat(Formula index) => Call("Matrix", index, index, Complex);
    private static Formula Space(Formula index) => Call("Workspace", index);
    private static Formula Tree(Formula index, Formula depth) => Call("Protocol", index, depth);
    private static Formula Hist(Formula tree) => Call("History", tree);
    private static Formula Leaf => At(new Formula.Subscript(V("leaf"), V("R")), V("b"));
    private static Formula NodeTree => Call("node", V("k"), V("U"), V("P"), V("c"));
    private static Formula Child => At(V("c"), V("o"));
    private static Formula K(Formula tree, Formula prefix, Formula history, Formula ancilla) =>
        Call("krausFrom", tree, prefix, history, ancilla);
    private static Formula Adj(Formula value) => Call("adjoint", value);
    private static Formula MatrixOf(Formula value) => At(Call("symm", V("ofMatrix")), value);
    private static Formula ChannelAction(Formula channel, Formula value) =>
        MatrixOf(At(Call("toCompletelyPositiveMap", channel), Call("ofMatrix", value)));
    private static Formula.BoundVariable B(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], Parenthesized(body));
    private static Formula Some(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], Parenthesized(body));
    private static Formula SumOver(string name, Formula domain, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Typed(V(name), domain)), Sp, Parenthesized(body));
    private static Formula SigmaOver(string name, Formula domain, Formula body) =>
        Seq(Sigma, Underscore, Grp(Typed(V(name), domain)), Sp, Parenthesized(body));
    private static Formula System(Formula body) => All(
        [B("I", V("Type"))], Imp(And(Call("Nonempty", Call("Fintype", V("I"))),
            Call("Nonempty", Call("DecidableEq", V("I")))), body));
    private static Formula OnTree(Formula body) => System(All(
        [B("R", N), B("t", Tree(V("I"), V("R")))], body));
    private static Formula OnLeaf(Formula body) => All([B("R", N), B("b", V("Bool"))], body);
    private static Formula OnNode(Formula body) => All(
        [B("R", N), B("k", N), B("U", Call("unitary", Space(V("I")))),
         B("P", Call("Measurement", V("I"), V("k"))),
         B("c", Arrow(Fin(V("k")), Tree(V("I"), V("R"))))], body);
    private static Formula OnNodeHistory(Formula body) => OnNode(All(
        [B("o", Fin(V("k"))), B("h", Hist(Child))], body));
    private static Formula FrameType(Formula n) => Call("FrameIndex", n);
    private static Formula FrameSize(Formula n) => Mul(n, n);
    private static Formula OrdinalFrameType(Formula n) => Fin(Call("card", FrameType(n)));

    private static Formula WorkspaceFormula()
    {
        Formula index = Product(V("I"), Fin(D(2)));
        return All([B("I", V("Type"))], EqTo(Space(V("I")), Call("CStarMatrix", index, index, Complex)));
    }

    private static Formula MeasurementFormula()
    {
        Formula i = V("I"), k = V("k"), p = V("P"), o = V("o"), z = V("z");
        Formula po = MatrixOf(At(p, o)), pz = MatrixOf(At(p, z));
        Formula laws = And(All([B("o", Fin(k))], EqTo(Adj(po), po)),
            And(All([B("o", Fin(k))], EqTo(Mul(po, po), po)),
                And(All([B("o", Fin(k)), B("z", Fin(k))], Imp(NeTo(o, z), EqTo(Mul(po, pz), D(0)))),
                    EqTo(SumOver("o", Fin(k), po), D(1)))));
        return System(All([B("k", N)], EqTo(Call("Measurement", i, k),
            SigmaOver("P", Arrow(Fin(k), Space(i)), laws))));
    }

    private static Formula ProtocolFormula() => System(And(
        OnLeaf(Typed(Leaf, Tree(V("I"), V("R")))),
        OnNode(Typed(NodeTree, Tree(V("I"), PlusTo(V("R"), D(1)))))));

    private static Formula HistoryFormula() => System(And(
        OnLeaf(EqTo(Hist(Leaf), V("Unit"))),
        OnNode(EqTo(Hist(NodeTree), SigmaOver("o", Fin(V("k")), Hist(Child))))));

    private static Formula HistoryFintypeFormula() => OnTree(
        Typed(Call("historyFintype", V("t")), Call("Fintype", Hist(V("t")))));

    private static Formula SucceedsFormula() => System(And(
        OnLeaf(All([B("u", V("Unit"))], EqTo(Call("succeeds", Leaf, V("u")), V("b")))),
        OnNodeHistory(EqTo(Call("succeeds", NodeTree, Pair(V("o"), V("h"))),
            Call("succeeds", Child, V("h"))))));

    private static Formula BranchFormula() => System(And(
        OnLeaf(All([B("u", V("Unit"))], EqTo(Call("branch", Leaf, V("u")), D(1)))),
        OnNodeHistory(EqTo(Call("branch", NodeTree, Pair(V("o"), V("h"))),
            Mul(Mul(Call("branch", Child, V("h")), Call("projector", V("P"), V("o"))), V("U"))))));

    private static Formula KrausFormula()
    {
        Formula t = V("t"), h = V("h"), a = V("a"), i = V("i"), j = V("j");
        Formula entry = At(K(t, V("B"), h, a), i, j);
        Formula compressed = At(MatrixOf(Mul(Call("branch", t, h), V("B"))), Pair(i, a), Pair(j, D(0)));
        Formula flag = Call("succeeds", t, h);
        return OnTree(All([B("B", Space(V("I"))), B("h", Hist(t)), B("a", Fin(D(2))),
            B("i", V("I")), B("j", V("I"))], And(
                Imp(EqTo(flag, V("true")), EqTo(entry, compressed)),
                Imp(EqTo(flag, V("false")), EqTo(entry, D(0))))));
    }

    private static Formula TreeMapFormula()
    {
        Formula t = V("t"), x = V("X"), kraus = K(t, D(1), V("h"), V("a"));
        return OnTree(All([B("X", Mat(V("I")))], EqTo(Call("successfulMap", t, x),
            SumOver("h", Hist(t), SumOver("a", Fin(D(2)), Mul(Mul(kraus, x), Adj(kraus)))))));
    }

    private static Formula RandomizedFormula() => System(All([B("R", N)],
        EqTo(Call("RandomizedProtocol", V("I"), V("R")),
            SigmaOver("N", N, Product(Call("StdSimplex", Real, Fin(V("N"))),
                Arrow(Fin(V("N")), Tree(V("I"), V("R"))))))));

    private static Formula RandomizedMapFormula()
    {
        Formula p = V("p"), s = V("s"), x = V("X");
        Formula weight = Call("ofReal", Call("weights", Call("probability", p), s));
        return System(All([B("R", N), B("p", Call("RandomizedProtocol", V("I"), V("R"))),
            B("X", Mat(V("I")))], EqTo(Call("mixtureMap", p, x),
                SumOver("s", Fin(Call("seeds", p)), Mul(weight, Call("successfulMap", Call("tree", p, s), x))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = V("d"), phi = V("Phi"), q = V("q"), x = V("X");
        Formula simulation = All([B("X", Mat(Fin(d)))], EqTo(Call("mixtureMap", V("p"), x),
            Mul(Call("ofReal", q), ChannelAction(phi, x))));
        return IffTo(V("claim"), Some([B("Rzero", N), B("qzero", Real)],
            And(LtTo(D(0), V("qzero")), All([B("d", N), B("Phi", Call("QuantumChannel", Fin(d), Fin(d)))],
                Some([B("p", Call("RandomizedProtocol", Fin(d), V("Rzero"))), B("q", Real)],
                    And(LeTo(V("qzero"), q), simulation))))));
    }

    private static Formula FrameIndexFormula()
    {
        Formula n = V("n"), columns = Fin(FrameSize(n));
        return All([B("n", N)], EqTo(FrameType(n), Call("Sum", columns, Arrow(columns, V("Bool")))));
    }

    private static Formula FrameFormula()
    {
        Formula n = V("n"), i = V("i"), j = V("j"), s = V("s"), columns = Fin(FrameSize(n));
        Formula basis = All([B("i", columns), B("j", columns)],
            EqTo(At(Call("frame", n), Call("inl", i), j), Call("ite", EqTo(i, j), D(1), D(0))));
        Formula signs = All([B("s", Arrow(columns, V("Bool"))), B("j", columns)],
            EqTo(At(Call("frame", n), Call("inr", s), j),
                new Formula.Fraction(Call("ofReal", Call("ite", At(s, j), D(1), new Formula.Negate(D(1)))),
                    Call("natCast", Complex, n))));
        return All([B("n", N)], And(basis, signs));
    }

    private static Formula FrameNatFormula()
    {
        Formula n = V("n"), i = V("i"), j = V("j");
        Formula original = At(Call("symm", Call("equivFin", FrameType(n))), i);
        return All([B("n", N), B("i", OrdinalFrameType(n)), B("j", Fin(FrameSize(n)))],
            EqTo(At(Call("frameNat", n), i, j), At(Call("frame", n), original, j)));
    }

    private static Formula FrameChannelBoundFormula()
    {
        Formula n = V("n"), index = OrdinalFrameType(n), x = V("X"), q = V("q");
        Formula diagonal = Call("diagonal", Seq(LambdaLower, Sp, Typed(V("i"), index), Comma, Sp,
            At(Call("frameNat", n), V("i"), V("j"))));
        Formula action = ChannelAction(V("Phi"), x);
        Formula definition = All([B("X", Mat(index))], EqTo(action,
            SumOver("j", Fin(FrameSize(n)), Mul(Mul(diagonal, x), Adj(diagonal)))));
        Formula exact = All([B("X", Mat(index))], EqTo(Call("mixtureMap", V("p"), x), Mul(Call("ofReal", q), action)));
        Formula bound = All([B("R", N), B("p", Call("RandomizedProtocol", index, V("R"))), B("q", Real)],
            Imp(exact, LeTo(Mul(q, Call("natCast", Real, n)), Mul(D(4), new Formula.Power(D(4), V("R"))))));
        return Disp(All([B("n", N)], Imp(LeTo(D(2), n),
            Some([B("Phi", Call("QuantumChannel", index, index))], And(definition, bound)))));
    }
}
