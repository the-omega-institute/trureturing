using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class BooleanRankThreeProtocolDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Separation/BooleanRankThreeProtocol.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Boolean rank-three task admits three messages per side while all four whole-class deletions remain unbalanced.",
        H("A Rank-Three Protocol Beyond Balanced Deletion"),
        Blocks(
            Node("table", "The original partial Boolean table", "Ftheta", TableFormula(),
                "Let X={0,...,7}, Y={0,...,5}, and V=X disjoint union Y. A table F maps "
                + "X times Y to Option Bool. A star is a missing, illegal pair, not a third output. "
                + "The legal domain D consists exactly of pairs with an entry. The simple bipartite "
                + "support G has vertex set V and one edge for each legal pair, with its original Boolean label.",
                DescribeRole.Definition),
            Node("protocol", "Arbitrary alphabets and reachable messages", "Protocol", ProtocolFormula(),
                "For arbitrary types A and B with decidable equality, alpha:X to A and beta:Y to B "
                + "are total encoders and delta:A to B to Bool is a total decoder. A and B may be infinite. "
                + "Only their finite reachable images are charged. Correctness is required exactly on legal "
                + "pairs; decoder values at unreachable message pairs are unrestricted.", DescribeRole.Definition),
            Node("decoder", "The explicit three-message protocol", "delta", EncodingFormula(),
                "Here A=B=Nat. The encoder strings, in increasing input order, are 01101002 and 001221. "
                + "The displayed decoder rows are 001, 100 and 010, indexed by messages 0,1,2. "
                + "All other ambient message pairs have decoder value false. Each encoder reaches exactly "
                + "the three symbols 0,1,2. The following sixteen rows list (input pair, message pair, "
                + "decoded bit, target bit); they exhaust the original legal domain.", DescribeRole.Definition,
                Paragraph(Math(LegalChecks()))),
            Node("residual", "Whole original monochromatic classes", "residual", ResidualFormula(),
                "A vertex belongs to M_X^c or M_Y^d precisely when every incident edge in the original "
                + "legal domain has that bit. H_cd is the induced graph on all remaining vertices. "
                + "Every surviving isolated vertex remains in its vertex set. Labels are restricted "
                + "along this vertex inclusion; neither conflicts nor monochromatic classes are recomputed "
                + "after deletion. The original classes are M_X^0={0}, M_X^1={1}, M_Y^0={2}, M_Y^1={4}.",
                DescribeRole.Definition),
            Node("balance", "Balance on actual simple cycles", "Balanced", BalanceFormula(),
                "Balanced(F,c,d) means that every actual simple closed cycle in the induced residual "
                + "has label sum zero in ZMod 2. Odd refers to label parity, not cycle length. "
                + "The bipartite cycles below have length eight.", DescribeRole.Definition),
            Node("cycles", "Four surviving simple odd cycles", "cycleWalk", CycleFormula(),
                "The support is the union of four internally vertex-disjoint paths from y_0 to y_1: "
                + "P_0=(y_0,x_0,y_1), P_1=(y_0,x_1,y_1), "
                + "Q_0=(y_0,x_2,y_2,x_3,y_3,x_4,y_1), and "
                + "Q_1=(y_0,x_5,y_4,x_6,y_5,x_7,y_1). Their label words are respectively "
                + "00, 11, 100101 and 011010. For each c,d, traverse P_(1-c) then reverse Q_(1-d). "
                + "The resulting walk closes in H_cd, has eight distinct cyclic vertices, and has label "
                + "sum one. H_00 deletes x_0,y_2 and retains P_1 union Q_1; H_01 deletes x_0,y_4 "
                + "and retains P_1 union Q_0; H_10 deletes x_1,y_2 and retains P_0 union Q_1; "
                + "H_11 deletes x_1,y_4 and retains P_0 union Q_0.", DescribeRole.Definition),
            Node("data", "The complete concrete task data", "TaskData", DataFormula(),
                "TaskData is the conjunction of all displayed clauses. There are sixteen legal pairs, "
                + "sixteen support edges, and fourteen vertices. Every row and column is active, and the "
                + "support is connected. Cycle rank uses integer subtraction: 16-8-6+1=3. "
                + "In the original Alice conflict graph, x and x' are adjacent exactly when some common "
                + "legal y gives different labels; the Bob graph exchanges the coordinates. Their edge "
                + "sets are {01,02,04,15,17,25,34,47,67} and {02,04,13,15,23,45}, respectively. "
                + "The proper two-color strings are 01101010 and 011010. Both graphs have an edge, "
                + "so both original chromatic numbers are exactly two. The cycle clause includes both "
                + "simplicity and parity for each of the four deletions. The final two clauses give "
                + "the exact reachable image cardinalities.", DescribeRole.Definition),
            Node("claim", "The proposed necessity of balanced deletion", "claim", ClaimFormula(),
                "The claim says that the complete concrete task data and correctness of the displayed "
                + "protocol would force at least one of the four whole-class deletions to be balanced.",
                DescribeRole.Definition),
            Node("result", "A finite counterexample to deletion necessity", "result", NegatedClaimFormula(),
                "The negated implication is classically equivalent to the full positive conjunction: "
                + "TaskData holds, the explicit protocol is correct, and every one of the four deletions "
                + "fails balance. Thus no false antecedent accounts for the refutation. Connectivity "
                + "follows along the four paths. The two-colorings and an edge in each conflict graph "
                + "give the exact chromatic numbers. The table determines the original monochromatic "
                + "classes, and each displayed induced-residual simple cycle has parity one. "
                + "The sixteen legal-pair checks establish the protocol. These facts occur in the same "
                + "finite task. This counterexample does not assert a general rank-three feasibility theorem.",
                DescribeRole.Theorem, Paragraph(Math(ResultFormula()))))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, params DocumentBlock[] extra) =>
        Describe.Lean(DescribeId.Create("boolean-rank-three-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(prose)), .. extra]), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Sub(Formula f, Formula i) => Seq(f, Underscore, Grp(i));
    private static Formula App(Formula f, params Formula[] args) =>
        Seq(f, Open, Join(Comma, args), Close);
    private static Formula Join(Formula separator, params Formula[] values) =>
        Seq(values.SelectMany((value, i) => i == 0 ? new[] { value }
            : new[] { separator, Sp, value }).ToArray());
    private static Formula Gather(params Formula[] rows) =>
        Seq(Begin, Grp(V("gathered")), Join(RowBreak, rows), End, Grp(V("gathered")));
    private static Formula Set(params Formula[] values) => Seq(OpenBrace, Join(Comma, values), CloseBrace);
    private static Formula Card(Formula f) => Seq(Lvert, Sp, f, Rvert);
    private static Formula BoolSet => Set(D(0), D(1));
    private static Formula Ft => Sub(V("F"), Theta);
    private static Formula M(Formula side, Formula bit) =>
        Seq(Sub(V("M"), side), Caret, Grp(bit));
    private static Formula Hcd => Sub(V("H"), Seq(V("c"), V("d")));
    private static Formula Cd => App(V("C"), V("c"), V("d"));
    private static Formula ProtocolValue => App(V("Protocol"), Ft, D(3), D(3), Alpha, Beta, DeltaLower);
    private static Formula BalancedValue => App(V("Balanced"), Ft, V("c"), V("d"));
    private static Formula AllBits(Formula body) => Seq(Forall, Sp, V("c"), Comma, V("d"),
        InMacro, Sp, BoolSet, Comma, Sp, body);
    private static Formula SomeBalanced => Seq(Exists, Sp, V("c"), Comma, V("d"),
        InMacro, Sp, BoolSet, Comma, Sp, BalancedValue);

    private static Formula Matrix(params string[] rows) => Seq(Begin, Grp(V("pmatrix")),
        Join(RowBreak, rows.Select(row => Join(Amp, row.Select(ch => ch == '*'
            ? Star : D((byte)(ch - '0'))).ToArray())).ToArray()), End, Grp(V("pmatrix")));

    private static Formula TableFormula() => Disp(Seq(Ft, Eq,
        Matrix("00****", "11****", "1*0***", "**01**", "*1*0**", "0***1*", "****10", "*0***1")));

    private static Formula ProtocolFormula() => Disp(Seq(
        App(V("Protocol"), V("F"), V("p"), V("q"), Alpha, Beta, DeltaLower), Leftrightarrow, Sp,
        Card(App(Alpha, V("X"))), Leq, Sp, V("p"), Land, Sp,
        Card(App(Beta, V("Y"))), Leq, Sp, V("q"), Land, Sp,
        Forall, Sp, Par(Seq(V("x"), Comma, V("y"))), InMacro, Sp, V("D"), Comma,
        App(DeltaLower, App(Alpha, V("x")), App(Beta, V("y"))), Eq, App(V("f"), V("x"), V("y"))));

    private static Formula EncodingFormula() => Disp(Gather(
        Seq(Alpha, Eq, Par(Join(Comma, D(0), D(1), D(1), D(0), D(1), D(0), D(0), D(2)))),
        Seq(Beta, Eq, Par(Join(Comma, D(0), D(0), D(1), D(2), D(2), D(1)))),
        Seq(DeltaLower, Eq, Matrix("001", "100", "010"))));

    private static Formula LegalChecks()
    {
        int[][] checks = [
            [0,0,0,0,0], [0,1,0,0,0], [1,0,1,0,1], [1,1,1,0,1],
            [2,0,1,0,1], [2,2,1,1,0], [3,2,0,1,0], [3,3,0,2,1],
            [4,1,1,0,1], [4,3,1,2,0], [5,0,0,0,0], [5,4,0,2,1],
            [6,4,0,2,1], [6,5,0,1,0], [7,1,2,0,0], [7,5,2,1,1]];
        return Disp(Gather(checks.Select(v => Join(Semi,
            Par(Seq(D((byte)v[0]), Comma, D((byte)v[1]))),
            Par(Seq(D((byte)v[2]), Comma, D((byte)v[3]))),
            D((byte)v[4]), D((byte)v[4]))).ToArray()));
    }

    private static Formula ResidualFormula() => Disp(Gather(
        Seq(M(V("X"), V("c")), Eq, OpenBrace, V("x"), InMacro, Sp, V("X"), Mid,
            Forall, Sp, V("y"), Comma, Par(Seq(V("x"), Comma, V("y"))), InMacro, Sp, V("D"),
            Implies, Sp, App(V("f"), V("x"), V("y")), Eq, V("c"), CloseBrace),
        Seq(M(V("Y"), V("d")), Eq, OpenBrace, V("y"), InMacro, Sp, V("Y"), Mid,
            Forall, Sp, V("x"), Comma, Par(Seq(V("x"), Comma, V("y"))), InMacro, Sp, V("D"),
            Implies, Sp, App(V("f"), V("x"), V("y")), Eq, V("d"), CloseBrace),
        Seq(Hcd, Eq, V("G"), OpenBracket, V("V"), Setminus, Sp,
            Par(Seq(M(V("X"), V("c")), Cup, Sp, M(V("Y"), V("d")))), CloseBracket)));

    private static Formula BalanceFormula() => Disp(Seq(BalancedValue, Leftrightarrow, Sp,
        Forall, Sp, V("v"), InMacro, Sp, App(V("V"), Hcd), Comma,
        Forall, Sp, V("p"), InMacro, Sp, App(V("Walk"), Hcd, V("v"), V("v")), Comma,
        App(V("IsCycle"), V("p")), Implies, Sp, App(V("parity"), V("p")), Eq, D(0)));

    private static Formula CycleFormula() => Disp(Gather(
        Seq(Cd, Eq, Sub(V("P"), Seq(D(1), Minus, V("c"))), Cup, Sp,
            Sub(V("Q"), Seq(D(1), Minus, V("d")))),
        AllBits(Seq(App(V("IsCycle"), Cd), Land, Sp, App(V("parity"), Cd), Eq, D(1)))));

    private static Formula DataFormula() => Disp(Seq(V("TaskData"), Leftrightarrow, Sp, Par(Gather(
        Seq(Card(V("D")), Eq, D(1,6), Land, Sp, Card(App(V("E"), V("G"))), Eq, D(1,6), Land, Sp,
            Card(V("V")), Eq, D(1,4)),
        Seq(Land, Sp, Par(Seq(Forall, Sp, V("x"), InMacro, Sp, V("X"), Comma, Exists, Sp, V("y"),
            InMacro, Sp, V("Y"), Comma, Par(Seq(V("x"), Comma, V("y"))), InMacro, Sp, V("D")))),
        Seq(Land, Sp, Par(Seq(Forall, Sp, V("y"), InMacro, Sp, V("Y"), Comma, Exists, Sp, V("x"),
            InMacro, Sp, V("X"), Comma, Par(Seq(V("x"), Comma, V("y"))), InMacro, Sp, V("D")))),
        Seq(Land, Sp, App(V("Connected"), V("G")), Land, Sp,
            App(V("cycleRank"), Ft), Eq, D(3)),
        Seq(Land, Sp, App(V("chromaticNumber"), Sub(V("G"), V("A"))), Eq, D(2), Land, Sp,
            App(V("chromaticNumber"), Sub(V("G"), V("B"))), Eq, D(2)),
        Seq(Land, Sp, M(V("X"), D(0)), Eq, Set(D(0)), Land, Sp, M(V("X"), D(1)), Eq, Set(D(1))),
        Seq(Land, Sp, M(V("Y"), D(0)), Eq, Set(D(2)), Land, Sp, M(V("Y"), D(1)), Eq, Set(D(4))),
        Seq(Land, Sp, Par(AllBits(Seq(App(V("IsCycle"), Cd), Land, Sp, App(V("parity"), Cd), Eq, D(1))))),
        Seq(Land, Sp, Card(App(Alpha, V("X"))), Eq, D(3), Land, Sp, Card(App(Beta, V("Y"))), Eq, D(3))))));

    private static Formula ClaimFormula() => Disp(Seq(V("claim"), Leftrightarrow, Sp,
        Par(Seq(V("TaskData"), Implies, Sp, Par(Seq(ProtocolValue, Implies, Sp, SomeBalanced))))));

    private static Formula NegatedClaimFormula() => Disp(
        Seq(Neg, Sp, Par(Seq(V("TaskData"), Implies, Sp, Par(Seq(ProtocolValue, Implies, Sp, SomeBalanced))))));

    private static Formula ResultFormula() => Disp(Gather(
        Seq(Neg, Sp, Par(Seq(V("TaskData"), Implies, Sp, Par(Seq(ProtocolValue, Implies, Sp, SomeBalanced))))),
        Seq(Leftrightarrow, Sp, Par(Seq(V("TaskData"), Land, Sp, ProtocolValue, Land, Sp,
            Par(AllBits(Seq(Neg, Sp, BalancedValue))))))));
}
