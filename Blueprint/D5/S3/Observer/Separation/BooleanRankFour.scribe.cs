using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class BooleanRankFourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Boolean task of cyclomatic rank four determines the exact ordered message budgets for every higher rank bound.",
        H("Boolean Tasks at Cyclomatic Rank Four"),
        Blocks(
            Paragraph(Text(
                "In the definitions, X and Y are arbitrary types, T is a task on X and Y, "
                + "x,u range over X, y,v range over Y, p,q are natural numbers, and s is "
                + "an integer. Boolean values 0 and 1 "
                + "mean false and true. Finiteness of the input types is imposed in the "
                + "uniform class below. Message alphabets may be arbitrary types. "
                + "For finite inputs, budgets count distinct messages actually sent, "
                + "and are upper bounds.")),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-task"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.Task"),
                H("A partial Boolean task"),
                StatementSource.FromAuthor(Disp(Gather(
                    Rel(App("Task", X, Y), Eq, Arrow(X, Arrow(Y, App("Option", Bits)))),
                    Rel(Legal, Eq, SetWhere(Tuple(x, y), Seq(
                        Rel(x, InMacro, X), Comma, Rel(y, InMacro, Y), Comma,
                        Ex(c, Bits, LegalValue(x, y, c)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Task(X,Y) is the type X -> Y -> Option Bool. The value none means "
                    + "that the pair is illegal; some(c) means it is legal with output c. "
                    + "D(T) denotes the set of legal pairs. No condition is imposed on "
                    + "a protocol's answer at an illegal pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-left-conflict"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.leftConflict"),
                H("The original left conflict graph"),
                StatementSource.FromAuthor(Disp(Rel(
                    App("Adj", App("leftConflict", T), x, V("u")), Iff,
                    Ex(y, Y, Ex(Seq(c, Comma, V("e")), Bits, And(
                        LegalValue(x, y, c), LegalValue(V("u"), y, V("e")),
                        Rel(c, Neq, V("e")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vertices are X. Two rows are adjacent exactly when one common "
                    + "column is legal in both and has different Boolean outputs. "
                    + "This symmetric, loopless graph depends only on the original task."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-right-conflict"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.rightConflict"),
                H("The original right conflict graph"),
                StatementSource.FromAuthor(Disp(Rel(
                    App("Adj", App("rightConflict", T), y, V("v")), Iff,
                    Ex(x, X, Ex(Seq(c, Comma, V("e")), Bits, And(
                        LegalValue(x, y, c), LegalValue(x, V("v"), V("e")),
                        Rel(c, Neq, V("e")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vertices are Y. Two columns conflict when a common legal row "
                    + "gives different outputs. Equivalently, this is the left conflict "
                    + "graph of the transposed task. Both chromatic hypotheses below "
                    + "refer to these original graphs, before any messages are chosen."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-support"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.support"),
                H("The bipartite support"),
                StatementSource.FromAuthor(Disp(Rel(App("support", T), Eq, Tuple(
                    App("Sum", X, Y), SetWhere(Set(App("inl", x), App("inr", y)),
                        Rel(Tuple(x, y), InMacro, Legal)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vertex set is the disjoint union X plus Y. An undirected edge "
                    + "joins inl(x) to inr(y) precisely when (x,y) is legal. There are "
                    + "no edges within either side; the Boolean label does not affect support."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-active-connected"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.ActiveConnected"),
                H("All inputs active, with nonempty connected support"),
                StatementSource.FromAuthor(Disp(Rel(App("ActiveConnected", T), Iff, And(
                    App("Nonempty", Legal),
                    Par(All(x, X, Ex(y, Y, Rel(Tuple(x, y), InMacro, Legal)))),
                    Par(All(y, Y, Ex(x, X, Rel(Tuple(x, y), InMacro, Legal)))),
                    App("Connected", App("support", T)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At least one legal pair exists, every x has a legal partner, "
                    + "every y has a legal partner, and the support graph is connected. "
                    + "Thus both input types are nonempty and contain exactly active inputs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-cycle-rank"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.cycleRank"),
                H("Integer cyclomatic rank"),
                StatementSource.FromAuthor(Disp(Seq(
                    App("cycleRank", T), Eq, App("NatCard", Legal), Minus,
                    App("NatCard", X), Minus, App("NatCard", Y), Plus, D(1), InMacro, Integers))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "NatCard denotes Nat.card: the finite cardinality of a type, and "
                    + "zero for an infinite type. Each cardinality is coerced to the "
                    + "integers before subtraction. For finite active connected support "
                    + "this is the cyclomatic number |D(T)|-|X|-|Y|+1; subtraction is "
                    + "not truncated at zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-admits"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.Admits"),
                H("Reachable message budgets and a total decoder"),
                StatementSource.FromAuthor(Disp(AdmitsFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There exist arbitrary types A and B, encoders a:X->A and b:Y->B, "
                    + "and a total decoder d:A->B->Bool. Only Nat.card(range(a)) and "
                    + "Nat.card(range(b)) are charged. For every x, y and Boolean c, "
                    + "T(x,y)=some(c) requires d(a(x),b(y))=c. The decoder is defined "
                    + "even on unreachable message pairs. Neither encoder must be "
                    + "surjective onto its ambient alphabet. With finite inputs, both "
                    + "reachable images are finite even if A or B is infinite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-region"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.Region"),
                H("The ordered budget region"),
                StatementSource.FromAuthor(Disp(Rel(App("Region", p, q), Iff, RegionFormula()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Alice has budget p and Bob has budget q. Each budget is at least "
                    + "two and at least one is at least four. Equivalently, this is "
                    + "the union of p>=2,q>=4 and p>=4,q>=2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-uniform"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.Uniform"),
                H("A uniform bound over all finite input types"),
                StatementSource.FromAuthor(Disp(UniformFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every pair of types X,Y with finite enumerations, and every "
                    + "task on them, assume ActiveConnected(T), cycleRank(T)<=s, and "
                    + "chromatic number at most two for each original conflict graph. "
                    + "Uniform(s,p,q) requires Admits(T,p,q) for every such task. "
                    + "The alphabets, encoders and decoder may be chosen separately "
                    + "for each task. The chromatic bounds permit one used color and "
                    + "unused colors; they do not require chromatic number exactly two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-matrix"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.F4"),
                H("The six by five task"),
                StatementSource.FromAuthor(Disp(Gather(
                    Seq(Four, Colon, App("Task", App("Fin", D(6)), App("Fin", D(5)))),
                    Rel(Four, Eq, TaskMatrix())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Rows are indexed 0 through 5 and columns 0 through 4. A dash "
                    + "denotes none; 0 and 1 denote some(false) and some(true). "
                    + "The six rows have respectively 2,3,2,2,3,2 legal entries, "
                    + "so there are fourteen support edges on eleven vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-rank-four-result"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankFour.result"),
                H("Exact individual and uniform regions"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The six conclusions hold together: F4 is active and connected, "
                        + "its integer cycle rank is four, each original conflict graph "
                        + "has chromatic number exactly two, its individual region is "
                        + "Region(p,q) for every natural p,q, and the same equivalence "
                        + "holds uniformly for every integer s>=4 and every natural p,q.")),
                    Paragraph(Text(
                        "For the upper bound, take any finite task whose left conflict "
                        + "graph has a coloring a:X->Fin 2. For each y and color i, "
                        + "set b(y)(i) to the common output among legal rows of color i "
                        + "in column y, or to false when there is no such row. Two "
                        + "different outputs in one color would contradict proper "
                        + "coloring. The actual message alphabets are Fin 2 and "
                        + "Fin 2->Bool, with decoder d(i,t)=t(i). They have respectively "
                        + "two and four elements, so their reachable images give (2,4). "
                        + "Transposing the task gives (4,2). Enlarging either budget "
                        + "gives every point in Region.")),
                    Paragraph(Text(
                        "An entirely unused color, or a color absent from a particular "
                        + "column, simply receives the default false coordinate. A "
                        + "one-color task is included; neither endpoint requires both "
                        + "colors or all four response words to occur. This construction "
                        + "also permits empty input types, although ActiveConnected "
                        + "excludes them from the uniform class. It uses no rank bound.")),
                    Paragraph(Text(
                        "For F4, proper left and right colorings are (0,0,0,1,1,1) "
                        + "and (0,0,1,1,1). Rows 0 and 3 conflict at column 0, and "
                        + "columns 0 and 2 conflict at row 0, so both chromatic numbers "
                        + "are exactly two. Every vertex is active. Starting at column "
                        + "0 reaches rows 0,2,3,5; row 2 reaches column 3, which reaches "
                        + "rows 1,4. Rows 1 and 0 reach all remaining columns. The "
                        + "support is connected, and its rank is 14-6-5+1=4.")),
                    Paragraph(Text(
                        "For any finite input type and encoder a with at most k "
                        + "reachable messages, inject the finite type range(a) into "
                        + "Fin k and compose with x mapping to a(x) in that range. "
                        + "The resulting encoder a' satisfies a'(x)=a'(u) exactly "
                        + "when a(x)=a(u). This relabels only the reachable image; "
                        + "it puts no finiteness condition on the ambient alphabet "
                        + "and preserves every message collision.")),
                    Paragraph(Text(
                        "Correctness forces each encoder to separate adjacent vertices "
                        + "of its original conflict graph: a shared message at two "
                        + "opposite legal outputs would give the same decoder input "
                        + "two values. Relabeling therefore gives p>=2 and q>=2 "
                        + "for F4. To rule out both budgets at most three, relabel "
                        + "both reachable images into Fin 3. The complete list of "
                        + "left conflict edges is (0,3),(0,5),(1,3),(1,4),(2,3), "
                        + "(2,4),(2,5). Up to equality of color classes, every proper "
                        + "map of the six rows into Fin 3 is one of the nine rows "
                        + "below. In each row the first tuple is the normalized "
                        + "Alice partition P_k and the second is an ordered tuple C_k "
                        + "of four distinct Bob columns; k runs from 0 to 8.")),
                    Paragraph(Math(Disp(Partitions()))),
                    Paragraph(Text(
                        "Normalization labels classes in order of first occurrence, "
                        + "without changing which rows have equal messages. The nine "
                        + "tuples exhaust the equality partitions of assignments of "
                        + "six labels in Fin 3 satisfying those seven inequalities. For each k, the "
                        + "following six entries give row pairs (i,t), in the column "
                        + "position order (0,1),(0,2),(0,3),(1,2),(1,3),(2,3). "
                        + "An entry at positions (j,l) has P_k(i)=P_k(t), with "
                        + "F4(i,C_k(j)) and F4(t,C_k(l)) both legal and opposite. "
                        + "Thus the table supplies all 9 times 6 = 54 witnesses.")),
                    Paragraph(Math(Disp(CollisionRows()))),
                    Paragraph(Text(
                        "Fix k and any two distinct selected columns. If Bob gave "
                        + "them the same message, their displayed row pair would "
                        + "also have equal Alice messages. For their opposite legal "
                        + "values c and e, correctness would force the equality "
                        + "below. This is impossible for any decoder. The reverse "
                        + "column order uses the reversed row pair.")),
                    Paragraph(Math(Disp(CollisionFormula()))),
                    Paragraph(Text(
                        "Consequently all four selected Bob columns require distinct "
                        + "messages: their induced incompatibilities form a K4 for "
                        + "this Alice partition. This K4 is distinct from the original "
                        + "right conflict graph, whose chromatic number is two. "
                        + "An injection from these four columns into Fin 3 is "
                        + "impossible. Hence max(p,q)>=4, completing the individual "
                        + "equivalence for all natural budgets, including zero and one. "
                        + "The boundary points (2,4) and (4,2) are feasible; (3,3) "
                        + "and all pairs with either budget below two are infeasible.")),
                    Paragraph(Text(
                        "For every integer s>=4, this same F4 belongs to the entire "
                        + "class with cycleRank(T)<=s. Any uniform budget must "
                        + "therefore satisfy its individual lower bound. Conversely, "
                        + "the two response-word constructions work for every finite "
                        + "task with the two original chromatic bounds. This proves "
                        + "the full uniform equivalence without restricting input sizes "
                        + "or choosing only one endpoint orientation."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Join(Formula separator, params Formula[] values) =>
        Seq(values.SelectMany((value, i) => i == 0 ? new[] { value }
            : new[] { Sp, separator, Sp, value }).ToArray());
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Tuple(params Formula[] values) => Par(Join(Comma, values));
    private static Formula App(string name, params Formula[] values) => Seq(Op(name), Tuple(values));
    private static Formula Set(params Formula[] values) => Seq(OpenBrace, Join(Comma, values), CloseBrace);
    private static Formula SetWhere(Formula value, Formula condition) =>
        Seq(OpenBrace, value, Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(left, Sp, relation, Sp, right);
    private static Formula And(params Formula[] clauses) => Join(Land, clauses);
    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula All(Formula variables, Formula type, Formula body) =>
        Seq(Forall, Sp, variables, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(Formula variables, Formula type, Formula body) =>
        Seq(Exists, Sp, variables, Colon, Sp, type, Comma, Sp, body);
    private static Formula Gather(params Formula[] rows) =>
        Seq(Begin, Grp(V("gathered")), Join(RowBreak, rows), End, Grp(V("gathered")));
    private static Formula Matrix(params Formula[] rows) =>
        Seq(Begin, Grp(V("pmatrix")), Join(RowBreak, rows), End, Grp(V("pmatrix")));
    private static Formula Row(params Formula[] entries) => Join(Amp, entries);
    private static Formula Nums(params byte[] entries) => Tuple(entries.Select(value => D(value)).ToArray());
    private static Formula X => V("X");
    private static Formula Y => V("Y");
    private static Formula T => V("T");
    private static Formula x => V("x");
    private static Formula y => V("y");
    private static Formula c => V("c");
    private static Formula p => V("p");
    private static Formula q => V("q");
    private static Formula s => V("s");
    private static Formula Bits => Op("Bool");
    private static Formula Types => Op("Type");
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers => Seq(Mathbb, Grp(V("Z")));
    private static Formula Four => new Formula.Subscript(V("F"), D(4));
    private static Formula Legal => App("D", T);
    private static Formula LegalValue(Formula row, Formula col, Formula value) =>
        Rel(App("T", row, col), Eq, App("some", value));
    private static Formula Chi(string graph, Formula task) => App("chromaticNumber", App(graph, task));
    private static Formula RegionFormula() => And(
        Rel(D(2), Leq, p), Rel(D(2), Leq, q), Rel(D(4), Leq, App("max", p, q)));

    private static Formula AdmitsFormula()
    {
        Formula a = V("a"), b = V("b"), d = V("d"), A = V("A"), B = V("B");
        Formula correct = All(x, X, All(y, Y, All(c, Bits, Rel(
            LegalValue(x, y, c), Implies, Rel(App("d", App("a", x), App("b", y)), Eq, c)))));
        return Rel(App("Admits", T, p, q), Iff,
            Ex(Seq(A, Comma, B), Types, Ex(a, Arrow(X, A), Ex(b, Arrow(Y, B),
            Ex(d, Arrow(A, Arrow(B, Bits)), And(
                Rel(App("NatCard", App("range", a)), Leq, p),
                Rel(App("NatCard", App("range", b)), Leq, q), Par(correct)))))));
    }

    private static Formula UniformFormula() => Rel(App("Uniform", s, p, q), Iff,
        All(Seq(X, Comma, Y), Types,
        Rel(And(App("Fintype", X), App("Fintype", Y)), Implies,
        All(T, App("Task", X, Y), Rel(Par(And(
            App("ActiveConnected", T), Rel(App("cycleRank", T), Leq, s),
            Rel(Chi("leftConflict", T), Leq, D(2)),
            Rel(Chi("rightConflict", T), Leq, D(2)))), Implies, App("Admits", T, p, q))))));

    private static Formula TaskMatrix() => Matrix(
        Row(D(1), Minus, D(0), Minus, Minus),
        Row(Minus, D(0), Minus, D(1), D(1)),
        Row(D(1), Minus, Minus, D(1), Minus),
        Row(D(0), Minus, Minus, D(0), Minus),
        Row(Minus, D(1), D(0), D(0), Minus),
        Row(D(0), Minus, Minus, Minus, D(1)));

    private static Formula ResultFormula() => Gather(
        And(App("ActiveConnected", Four), Rel(App("cycleRank", Four), Eq, D(4))),
        Seq(Land, Sp, And(Rel(Chi("leftConflict", Four), Eq, D(2)),
            Rel(Chi("rightConflict", Four), Eq, D(2)))),
        Seq(Land, Sp, Par(All(Seq(p, Comma, q), Naturals,
            Rel(App("Admits", Four, p, q), Iff, App("Region", p, q))))),
        Seq(Land, Sp, Par(All(s, Integers, Rel(Rel(D(4), Leq, s), Implies,
            All(Seq(p, Comma, q), Naturals,
                Rel(App("Uniform", s, p, q), Iff, App("Region", p, q))))))));

    private static Formula Partitions() => Matrix(
        Row(Nums(0, 0, 0, 1, 1, 1), Nums(0, 1, 2, 4)),
        Row(Nums(0, 0, 0, 1, 1, 2), Nums(0, 1, 2, 4)),
        Row(Nums(0, 0, 0, 1, 2, 1), Nums(0, 1, 2, 4)),
        Row(Nums(0, 0, 0, 1, 2, 2), Nums(0, 1, 2, 4)),
        Row(Nums(0, 0, 1, 2, 2, 2), Nums(0, 1, 2, 4)),
        Row(Nums(0, 1, 0, 2, 2, 2), Nums(0, 1, 2, 4)),
        Row(Nums(0, 1, 1, 2, 2, 2), Nums(0, 1, 2, 4)),
        Row(Nums(0, 1, 0, 2, 2, 1), Nums(0, 1, 2, 3)),
        Row(Nums(0, 1, 1, 2, 0, 2), Nums(0, 1, 3, 4)));

    private static Formula CollisionRows() => Matrix(
        Row(Nums(0, 1), Nums(0, 0), Nums(3, 5), Nums(4, 4), Nums(1, 1), Nums(0, 1)),
        Row(Nums(0, 1), Nums(0, 0), Nums(5, 5), Nums(4, 4), Nums(1, 1), Nums(0, 1)),
        Row(Nums(0, 1), Nums(0, 0), Nums(3, 5), Nums(4, 4), Nums(1, 1), Nums(0, 1)),
        Row(Nums(0, 1), Nums(0, 0), Nums(5, 5), Nums(4, 4), Nums(1, 1), Nums(0, 1)),
        Row(Nums(0, 1), Nums(0, 0), Nums(3, 5), Nums(4, 4), Nums(1, 1), Nums(0, 1)),
        Row(Nums(3, 4), Nums(0, 0), Nums(3, 5), Nums(4, 4), Nums(1, 1), Nums(4, 5)),
        Row(Nums(2, 1), Nums(0, 0), Nums(3, 5), Nums(4, 4), Nums(1, 1), Nums(4, 5)),
        Row(Nums(3, 4), Nums(0, 0), Nums(5, 1), Nums(4, 4), Nums(1, 1), Nums(0, 2)),
        Row(Nums(2, 1), Nums(0, 4), Nums(3, 5), Nums(1, 1), Nums(1, 1), Nums(3, 5)));

    private static Formula CollisionFormula()
    {
        Formula j = V("j"), l = V("l"), i = V("i"), t = V("t"), k = V("k");
        Formula cj = Seq(new Formula.Subscript(V("C"), k), Tuple(j));
        Formula cl = Seq(new Formula.Subscript(V("C"), k), Tuple(l));
        return Join(Eq, c, App("d", App("a", i), App("b", cj)),
            App("d", App("a", t), App("b", cl)), V("e"));
    }
}
