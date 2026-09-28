using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class BooleanRankThreeFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole original bit-class deletion gives a sufficient protocol construction and a necessary rank-three odd-fiber shape.",
        H("Boolean Tasks and the Complete Rank-Three Odd Fiber"),
        Blocks(
            Paragraph(Text(
                "Let X and Y be finite sets and let T:X times Y -> Option(F_2) be a partial Boolean table. "
                + "Write mathcal F for the class of finite sets and T(X,Y) for all such partial tables. "
                + "The value none denotes an illegal pair; some c assigns the bit c to a legal pair. "
                + "Write D for the legal pairs and f for their labels. The original support G is the simple "
                + "bipartite graph on the disjoint union of X and Y, with one edge for each pair in D. "
                + "Admissibility A(T) means that every vertex on both sides has an incident legal edge, "
                + "D is nonempty, G is connected, and both original conflict graphs have chromatic number "
                + "at most two. Two X vertices conflict exactly when they have different legal labels at "
                + "one common Y vertex; the definition on Y is symmetric. The one-way message costs equal "
                + "these chromatic numbers. The rank mu(T)=|D|-|X|-|Y|+1 is an integer.")),
            Paragraph(Text(
                "A budget B(T) means that there exist arbitrary ambient message types A and B, encoders "
                + "alpha:X->A and beta:Y->B, and a total decoder delta:A times B->F_2, with at most three "
                + "reachable messages on each side. Only the images of the encoders incur cost. Correctness "
                + "is required on every legal pair, and there is no restriction on illegal pairs. "
                + "Each encoder sees only its own input, and the decoder sees only the two messages.")),
            Paragraph(Math(Budget())),
            Paragraph(Text(
                "For c,d in F_2, M_X^c and M_Y^d are the entire original globally monochromatic bit "
                + "classes. Membership tests every original incident legal edge, including edges outside "
                + "a chosen cycle. Form H_cd by deleting both whole classes. Equivalently, retain the "
                + "original vertex carrier and isolate the deleted vertices; this preserves all surviving "
                + "simple cycles. These classes are fixed from T before deletion. They are neither "
                + "completed response classes nor classes recomputed from the residual graph.")),
            Paragraph(Math(Deletion())),
            Paragraph(Text(
                "A support subgraph is balanced when every simple cycle has label sum zero in F_2. "
                + "Thus odd means label parity one, although all cycle lengths in this bipartite graph "
                + "are even. Let U(T) mean that all four H_cd are unbalanced. Let Z(G) be the binary "
                + "cycle space, realized as the span of the edge indicators of actual simple cycles. "
                + "For z in Z(G), lambda(z) is the sum over original edges of f(e) times z(e).")),
            Paragraph(Text(
                "The shape S(T) consists of simple cycles C_ij indexed by all four pairs (i,j) in F_2 "
                + "times F_2. Their edge indicators z_ij must be pairwise distinct, and the whole original "
                + "odd fiber must equal their set. Each C_ij contains an original monochromatic X vertex "
                + "of bit i and an original monochromatic Y vertex of bit j. Every original monochromatic "
                + "X vertex on that cycle has bit i, and every original monochromatic Y vertex on it has "
                + "bit j. The four indicators sum to zero and their linear span has dimension three. "
                + "Cycles are distinguished by edge indicators, independently of starting point or orientation.")),
            Paragraph(Math(Shape())),
            Describe.Lean(
                DescribeId.Create("boolean-rank-three-fiber"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanRankThreeFiber.result"),
                H("Balanced deletion, the complete odd fiber, and failure of sufficiency"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The universal assertion ranges over every finite X and Y with decidable equality "
                        + "and every admissible partial Boolean table T on them. If some H_cd is balanced, "
                        + "then B(T) holds. If all four are unbalanced, mu(T)>=3, and equality forces S(T). "
                        + "In particular, the absence of a (3,3) protocol implies the same rank bound and "
                        + "the same conditional shape. The existential assertion concerns a table on "
                        + "Fin 8 times Fin 6: it is admissible, has rank three, satisfies U(T) and S(T), "
                        + "and nevertheless has a (3,3) protocol. Thus the rank-three shape is necessary "
                        + "for infeasibility but is not sufficient. No assertion of feasibility for every "
                        + "rank-three task follows.")),
                    Paragraph(Text(
                        "For a balanced H_cd, the cycle-space potential theorem gives a vertex potential "
                        + "whose endpoint sum equals each surviving edge label. Each surviving vertex "
                        + "sends its potential bit, and every vertex in the deleted class on a side sends "
                        + "one special message. Decode ordinary pairs by addition in F_2, a special Alice "
                        + "message by c, and a special Bob message by d. When both are special, any legal "
                        + "edge forces c=d; if c differs from d, that corner has no legal edge. This proves "
                        + "correctness on all original legal pairs using at most three messages per side, "
                        + "regardless of the sizes of the deleted classes.")),
                    Paragraph(Text(
                        "A proper two-coloring of Bob's original conflict graph makes each nonmonochromatic "
                        + "row equal, on its legal entries, to a row-dependent bit plus Bob's color. If an "
                        + "odd simple cycle contained no original globally monochromatic X vertex, these "
                        + "edge labels would telescope around the cycle to zero. This is impossible. "
                        + "The symmetric argument supplies an original globally monochromatic Y vertex. "
                        + "Choose C_ij in H_(1-i,1-j). Its original monochromatic vertices can only have "
                        + "the remaining bits i and j. The witnesses on both sides then force distinct "
                        + "indicators for distinct index pairs: equal indicators give equal edge sets "
                        + "and hence equal vertex supports.")),
                    Paragraph(Text(
                        "The graph-to-linear correspondence uses the actual support. Sending a legal "
                        + "pair (x,y) to the unordered edge joining its two tagged vertices is a bijection. "
                        + "Connectedness gives exactly one component, so the finite-graph cycle-space "
                        + "dimension formula yields dim Z(G)=|D|-|X|-|Y|+1=mu(T). A simple cycle traverses "
                        + "each of its edges once. Consequently the coordinate pairing defining lambda "
                        + "on its indicator is exactly the sum of its walk labels, without multiplicity "
                        + "or orientation ambiguity.")),
                    Paragraph(Text(
                        "All four chosen indicators lie in lambda^(-1)(1), so lambda is nonzero. "
                        + "Translation by one of them identifies this fiber with ker lambda, whose "
                        + "dimension is dim Z(G)-1. Its cardinality is therefore 2^(dim Z(G)-1). "
                        + "The injection from the four bit pairs gives mu(T)>=3. At rank three the "
                        + "fiber has exactly four elements, so this injection is surjective: it exhausts "
                        + "every original odd cycle-space vector, including any vector not initially "
                        + "presented as a simple cycle. A coset of a two-dimensional binary kernel has "
                        + "the form {z,z+u,z+v,z+u+v}; its four elements sum to zero and span the "
                        + "whole three-dimensional space. The infeasibility assertion is the "
                        + "contrapositive of the balanced-deletion construction followed by this argument.")),
                    Paragraph(Text(
                        "For nonsufficiency, take the following actual table; a star is an illegal pair.")),
                    Paragraph(Math(ConcreteTable())),
                    Paragraph(Text(
                        "Its support consists of four internally disjoint paths from y_0 to y_1: "
                        + "P_0=(y_0,x_0,y_1), P_1=(y_0,x_1,y_1), "
                        + "Q_0=(y_0,x_2,y_2,x_3,y_3,x_4,y_1), and "
                        + "Q_1=(y_0,x_5,y_4,x_6,y_5,x_7,y_1). Their label words are respectively "
                        + "00, 11, 100101, and 011010. All fourteen vertices are active and connected, "
                        + "and there are sixteen edges, giving rank 16-8-6+1=3. Proper colorings of the "
                        + "two original conflict graphs are 01101010 and 011010. The original bit classes "
                        + "are M_X^0={x_0}, M_X^1={x_1}, M_Y^0={y_2}, M_Y^1={y_4}. Each H_cd still "
                        + "contains the odd simple cycle P_(1-c) united with Q_(1-d). Thus all four "
                        + "residuals are unbalanced and the entire odd fiber consists of the four "
                        + "indicators of P_i united with Q_j.")),
                    Paragraph(Text(
                        "The actual encoders and decoder below use three reachable messages on each side. "
                        + "Substitution at each of the sixteen legal entries gives exactly its table bit. "
                        + "Hence the same task simultaneously has rank three, the entire four-cycle odd "
                        + "fiber, four unbalanced residuals, and an actual (3,3) protocol.")),
                    Paragraph(Math(ConcreteProtocol()))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula App(Formula name, params Formula[] args) => Seq(name, Open,
        Seq(args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray()), Close);
    private static Formula Set(Formula value) => Seq(OpenBrace, value, CloseBrace);
    private static Formula Abs(Formula value) => Seq(Lvert, value, Rvert);
    private static Formula Conj(params Formula[] values) => Seq(values.SelectMany((value, i) =>
        i == 0 ? new[] { value } : new[] { Land, Sp, value }).ToArray());
    private static Formula Gather(params Formula[] rows) => Seq(Begin, Grp(V("gathered")),
        Seq(rows.SelectMany((row, i) => i == 0 ? new[] { row } : new[] { RowBreak, row }).ToArray()),
        End, Grp(V("gathered")));
    private static Formula Bit => Sub(Seq(Mathbb, Grp(V("F"))), D(2));
    private static Formula Pred(string name, Formula t) => App(V(name), t);
    private static Formula Rank(Formula t) => App(Mu, t);
    private static Formula Mono(string side, Formula bit) => Pow(Sub(V("M"), V(side)), bit);
    private static Formula Cycle(Formula i, Formula j) => Sub(V("C"), Seq(i, j));
    private static Formula Indicator(Formula i, Formula j) => Sub(V("z"), Seq(i, j));
    private static Formula Residual(Formula c, Formula d) => Sub(V("H"), Seq(c, d));

    private static Formula Budget()
    {
        Formula x = V("x"), y = V("y"), t = V("T");
        return Disp(Seq(Pred("B", t), Iff, Exists, Sp, V("A"), Comma, V("B"), Comma,
            Alpha, Colon, V("X"), To, Sp, V("A"), Comma, Beta, Colon, V("Y"), To, Sp, V("B"), Comma,
            DeltaLower, Colon, V("A"), Times, Sp, V("B"), To, Bit, Comma, Sp,
            Conj(Seq(Abs(App(Alpha, V("X"))), Leq, D(3)),
                Seq(Abs(App(Beta, V("Y"))), Leq, D(3)),
                Par(Seq(Forall, Sp, Par(Seq(x, Comma, y)), InMacro, Sp, V("D"), Comma,
                    App(DeltaLower, App(Alpha, x), App(Beta, y)), Eq, App(V("f"), x, y))))));
    }

    private static Formula Deletion()
    {
        Formula x = V("x"), y = V("y"), c = V("c"), d = V("d");
        return Disp(Gather(
            Seq(Mono("X", c), Eq, Set(Seq(x, InMacro, Sp, V("X"), Mid, Forall, Sp, y, InMacro, Sp, V("Y"),
                Comma, Par(Seq(x, Comma, y)), InMacro, Sp, V("D"), Implies, Sp, App(V("f"), x, y), Eq, c))),
            Seq(Mono("Y", d), Eq, Set(Seq(y, InMacro, Sp, V("Y"), Mid, Forall, Sp, x, InMacro, Sp, V("X"),
                Comma, Par(Seq(x, Comma, y)), InMacro, Sp, V("D"), Implies, Sp, App(V("f"), x, y), Eq, d))),
            Seq(Residual(c, d), Eq, V("G"), Minus, Par(Seq(Mono("X", c), Cup, Sp, Mono("Y", d)))),
            Seq(Pred("U", V("T")), Iff, Forall, Sp, c, Comma, d, InMacro, Bit, Comma,
                Neg, Sp, Pred("Balanced", Residual(c, d)))));
    }

    private static Formula Shape()
    {
        Formula i = V("i"), j = V("j"), x = V("x"), y = V("y"), z = V("z");
        Formula support = App(V("V"), Cycle(i, j));
        Formula indexed = Set(Seq(Indicator(i, j), Mid, Sp, i, Comma, j, InMacro, Bit));
        return Disp(Gather(
            Seq(Pred("S", V("T")), Iff, Exists, Sp, V("C"), Colon, Pow(Bit, D(2)), To, Sp,
                App(V("Cycle"), V("G")), Comma),
            Par(Seq(Forall, Sp, i, Comma, j, Comma, V("k"), Comma, V("l"), InMacro, Bit,
                Comma, Indicator(i, j), Eq, Indicator(V("k"), V("l")), Implies,
                Par(Conj(Seq(i, Eq, V("k")), Seq(j, Eq, V("l")))))),
            Seq(Land, Par(Seq(Forall, Sp, z, InMacro, Sp, App(V("Z"), V("G")), Comma,
                App(LambdaLower, z), Eq, D(1), Iff, Exists, Sp, i, Comma, j, InMacro, Bit, Comma,
                Indicator(i, j), Eq, z))),
            Seq(Land, Par(Seq(Forall, Sp, i, Comma, j, InMacro, Bit, Comma,
                Par(Seq(Exists, Sp, x, InMacro, Sp, support, Comma, x, InMacro, Sp, Mono("X", i))), Land,
                Par(Seq(Exists, Sp, y, InMacro, Sp, support, Comma, y, InMacro, Sp, Mono("Y", j)))))),
            Seq(Land, Par(Seq(Forall, Sp, i, Comma, j, Comma, V("c"), InMacro, Bit, Comma,
                Forall, Sp, x, InMacro, Sp, support, Comma, x, InMacro, Sp, Mono("X", V("c")), Implies, Sp, V("c"), Eq, i))),
            Seq(Land, Par(Seq(Forall, Sp, i, Comma, j, Comma, V("d"), InMacro, Bit, Comma,
                Forall, Sp, y, InMacro, Sp, support, Comma, y, InMacro, Sp, Mono("Y", V("d")), Implies, Sp, V("d"), Eq, j))),
            Seq(Land, Sp, Indicator(D(0), D(0)), Plus, Indicator(D(0), D(1)), Plus,
                Indicator(D(1), D(0)), Plus, Indicator(D(1), D(1)), Eq, D(0), Land, Sp,
                Sub(V("dim"), Bit), Sub(V("span"), Bit), indexed, Eq, D(3))));
    }

    private static Formula Statement()
    {
        Formula t = V("T"), c = V("c"), d = V("d");
        Formula bound = Conj(Seq(D(3), Leq, Rank(t)),
            Par(Seq(Rank(t), Eq, D(3), Implies, Sp, Pred("S", t))));
        Formula universal = Seq(Forall, Sp, V("X"), Comma, V("Y"), InMacro,
            Seq(Mathcal, Grp(V("F"))), Comma, Forall, Sp, t, InMacro, Sp, App(V("T"), V("X"), V("Y")),
            Comma, Pred("A", t), Implies, Par(Conj(
                Par(Seq(Par(Seq(Exists, Sp, c, Comma, d, InMacro, Bit, Comma,
                    Pred("Balanced", Residual(c, d)))), Implies, Sp, Pred("B", t))),
                Par(Seq(Pred("U", t), Implies, Par(bound))),
                Par(Seq(Neg, Sp, Pred("B", t), Implies, Par(bound))))));
        Formula existential = Seq(Exists, Sp, t, InMacro, Sp, App(V("T"), App(V("Fin"), D(8)),
            App(V("Fin"), D(6))), Comma, Conj(Pred("A", t), Seq(Rank(t), Eq, D(3)),
                Pred("U", t), Pred("S", t), Pred("B", t)));
        return Disp(Gather(Par(universal), Land, Par(existential)));
    }

    private static Formula Matrix(params Formula[][] rows) => Seq(Begin, Grp(V("pmatrix")),
        Seq(rows.SelectMany((row, i) =>
            (i == 0 ? Array.Empty<Formula>() : new[] { RowBreak }).Concat(
                row.SelectMany((cell, j) => j == 0 ? new[] { cell } : new[] { Amp, cell }))).ToArray()),
        End, Grp(V("pmatrix")));

    private static Formula ConcreteTable()
    {
        Formula star = Star;
        return Disp(Seq(Sub(V("T"), Theta), Eq, Matrix(
            [D(0), D(0), star, star, star, star],
            [D(1), D(1), star, star, star, star],
            [D(1), star, D(0), star, star, star],
            [star, star, D(0), D(1), star, star],
            [star, D(1), star, D(0), star, star],
            [D(0), star, star, star, D(1), star],
            [star, star, star, star, D(1), D(0)],
            [star, D(0), star, star, star, D(1)])));
    }

    private static Formula ConcreteProtocol() => Disp(Gather(
        Seq(Alpha, Eq, Par(Seq(D(0), Comma, D(1), Comma, D(1), Comma, D(0), Comma,
            D(1), Comma, D(0), Comma, D(0), Comma, D(2)))),
        Seq(Beta, Eq, Par(Seq(D(0), Comma, D(0), Comma, D(1), Comma, D(2), Comma, D(2), Comma, D(1)))),
        Seq(DeltaLower, Eq, Matrix([D(0), D(0), D(1)], [D(1), D(0), D(0)], [D(0), D(1), D(0)]))));
}
