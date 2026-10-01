using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class BooleanLowCycleBudgetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected partial Boolean tasks with cycle rank at most two have an exact uniform region of ordered message budgets.",
        H("Exact Boolean Budgets at Low Cycle Rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partial-boolean-task"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.Task"),
                H("Partial Boolean tables"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary types X and Y, Task(X,Y) is the type of functions "
                    + "t:X -> Y -> Option(ZMod 2). Write mathbb B for ZMod 2, identified "
                    + "with the two bits 0 and 1; its addition is XOR. The legal domain "
                    + "D(t) consists exactly of the pairs (x,y) for which t(x,y) is not none. "
                    + "If t(x,y)=some(c), the required output on that pair is c. The value "
                    + "none means that the pair is illegal and imposes no output condition. "
                    + "It is not a third output. The classification below ranges over all "
                    + "finite X and Y and every such partial table."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bipartite-support"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.support"),
                H("Support with distinct input sides"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph support(t) has vertex type X disjoint-union Y. Its only "
                    + "edges join inl(x) to inr(y), and such an edge exists exactly when "
                    + "(x,y) belongs to D(t). Adjacency is symmetric, with no edges inside "
                    + "either side and no loops. Thus legal pairs correspond bijectively "
                    + "to its unordered edges, even when X and Y have common underlying values."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-left-conflicts"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.conflictLeft"),
                H("Original left conflicts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph conflictLeft(t) has vertices X. Two vertices x and u "
                    + "are adjacent exactly when there exist y in Y and bits c,d with "
                    + "t(x,y)=some(c), t(u,y)=some(d), and c different from d. Both pairs "
                    + "must be legal and the same y must occur in them. These conditions "
                    + "already exclude loops. Every correct left encoder separates "
                    + "adjacent vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-right-conflicts"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.conflictRight"),
                H("Original right conflicts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph conflictRight(t) is conflictLeft of the transposed table. "
                    + "Its vertices y and v are adjacent exactly when there exist x in X "
                    + "and distinct bits c,d with t(x,y)=some(c) and t(x,v)=some(d). "
                    + "Both conflict graphs use the original table, including all edges "
                    + "attached to a cycle. They are not recomputed from a smaller graph "
                    + "when edges are removed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reachable-message-budget"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.HasBudget"),
                H("Deterministic simultaneous messages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a table t and natural numbers p,q, HasBudget(t,p,q) means "
                        + "that there exist arbitrary message types A,B, maps alpha:X->A "
                        + "and beta:Y->B, and a total decoder delta:A->B->mathbb B. "
                        + "The natural cardinalities of the ranges of alpha and beta "
                        + "are at most p and q respectively. For every x in X, every "
                        + "y in Y, and every bit c, t(x,y)=some(c) implies "
                        + "delta(alpha(x),beta(y))=c.")),
                    Paragraph(Text(
                        "In the finite input setting both ranges are finite even if "
                        + "A or B is infinite. Only these reachable ranges are charged. "
                        + "Alice sees x alone, Bob sees y alone, and the decoder sees "
                        + "only their two messages. Correctness is required only on "
                        + "D(t); other message pairs may receive arbitrary Boolean "
                        + "values. There is no requirement to detect illegal inputs. "
                        + "Budgets are ordered upper bounds on symbol counts.")),
                    Paragraph(Text(
                        "For finite X,Y this definition is equivalent, for every p,q, "
                        + "to the existence of alpha:X->Fin p, beta:Y->Fin q and "
                        + "delta:Fin p->Fin q->mathbb B satisfying the same legal-pair "
                        + "equation. Embed each finite reachable range into its Fin "
                        + "alphabet. On pairs of embedded messages reconstruct the "
                        + "original messages and apply the original decoder; elsewhere "
                        + "choose zero. Injectivity makes reconstruction independent "
                        + "of the chosen preimages. Conversely, ranges inside Fin p "
                        + "and Fin q have at most p and q elements. This equivalence "
                        + "does not restrict the original message types."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("connected-low-rank-class"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.InClass"),
                H("The full class at a given cycle-rank bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite types X,Y, a table t and a natural number s, "
                        + "InClass(t,s) requires all of the following. For every x "
                        + "there exist y and c with t(x,y)=some(c), and for every y "
                        + "there exist x and c with t(x,y)=some(c). At least one "
                        + "legal pair exists. The support is connected. Each of "
                        + "the two original conflict graphs has chromatic number "
                        + "at most two. Finally, the integer cycle-rank expression "
                        + "below is at most s. Thus X and Y are precisely the "
                        + "nonempty active input sets; no size bound on either set "
                        + "is imposed.")),
                    Paragraph(Math(Rank())),
                    Paragraph(Text(
                        "Every cardinality in this expression is coerced to the "
                        + "integers before subtraction. In particular, neither "
                        + "subtraction is truncated at zero. The chromatic bounds "
                        + "also express the original one-sided message costs: a "
                        + "correct encoder is a proper coloring, while a proper "
                        + "coloring gives a decoder by taking the common output "
                        + "at a fixed opposite input and color. Empty entries of "
                        + "that response table can be filled arbitrarily."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-budget-region"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.UniformBudget"),
                H("A guarantee for every task in the class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural s,p,q, UniformBudget(s,p,q) means: for every type X "
                    + "with a finite enumeration, every type Y with a finite enumeration, "
                    + "and every t:Task(X,Y), InClass(t,s) implies HasBudget(t,p,q). "
                    + "The existential choice of alphabets, encoders and decoder occurs "
                    + "separately for each table after these universal quantifiers. "
                    + "Different tasks need not share a decoder. A particular task "
                    + "may admit smaller budgets than this guarantee for the whole class."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-edge-values"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.edgeValue"),
                H("Labels on unordered edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every unordered pair e of vertices in X disjoint-union Y, "
                    + "edgeValue(t,e) is the bit c if e joins x and y with "
                    + "t(x,y)=some(c), in either endpoint order. It is zero for "
                    + "illegal cross pairs and pairs within one side. The cycle "
                    + "arguments evaluate it only on edges of support subgraphs, "
                    + "where it agrees exactly with the original required output."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-low-cycle-budgets"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/BooleanLowCycleBudgets.result"),
                H("Exact ordered budgets for cycle ranks zero, one and two"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural s at most two and every pair of positive "
                        + "natural numbers p,q, the displayed equivalence gives the "
                        + "entire uniform budget region. Its minimal ordered pairs "
                        + "are (2,2) when s=0; (2,3) and (3,2) when s=1; and "
                        + "(2,4), (3,3) and (4,2) when s=2. Every coordinatewise "
                        + "larger pair belongs to the same region.")),
                    Paragraph(Text(
                        "Write G for the support and V for its full vertex set. "
                        + "The binary graph cycle-space theorem identifies its "
                        + "dimension with |E(G)|-|V|+k(G), where k counts connected "
                        + "components including isolated vertices. The legal-edge "
                        + "bijection and connectedness give dimension at most s. "
                        + "For any support subgraph H, all simple cycles have label "
                        + "XOR zero exactly when there is a potential h:V->mathbb B "
                        + "whose endpoint sums equal the edge labels. This applies "
                        + "component by component, with an independent root bit in "
                        + "each component and a free bit at every isolated vertex. "
                        + "A spanning forest constructs the potentials by path XOR; "
                        + "the remaining edges agree by their fundamental cycles.")),
                    Paragraph(Text(
                        "Fix proper Boolean colorings cx and cy of the original "
                        + "left and right conflict graphs. Define a completed "
                        + "two-bit response rx(x) on the colors of cy, and ry(y) "
                        + "on the colors of cx. Properness makes each occupied "
                        + "entry single-valued, and empty entries are assigned zero. "
                        + "Sending cx(x) and ry(y), with decoding by evaluation, "
                        + "gives (2,4). Sending rx(x) and cy(y) gives (4,2). "
                        + "These constructions work at every cycle rank.")),
                    Paragraph(Text(
                        "Every two-bit Boolean response is either constant or "
                        + "has the form j |-> r(0)+j. A constant rx(x) makes x "
                        + "monochromatic on all of its original legal edges; a "
                        + "nonconstant rx(x) satisfies f(x,y)=rx(x)(0)+cy(y) "
                        + "on every original legal edge. The analogous statement "
                        + "holds for ry(y). If a cycle has nonzero label XOR, "
                        + "its labels cannot all agree with the endpoint sums "
                        + "of the potential formed from rx(x)(0) and cy(y). "
                        + "An edge of disagreement therefore has an endpoint x "
                        + "with constant rx(x). Using cx(x) and ry(y)(0) gives "
                        + "such a y as well. Hence any nonzero-XOR cycle in any "
                        + "support subgraph contains a selectable vertex on either "
                        + "specified side that is monochromatic in the original "
                        + "table, including its attached edges.")),
                    Paragraph(Text(
                        "All cycle spaces can be compared inside the fixed space "
                        + "of Boolean functions on E(G): let K(H) be the span of "
                        + "the edge indicator vectors of simple cycles in H. "
                        + "Removing every edge incident to a chosen vertex a "
                        + "gives a subgraph cut(H,a), so K(cut(H,a)) is contained "
                        + "in K(H). If a lies on a cycle, select one incident "
                        + "cycle edge e. Every vector in K(cut(H,a)) has zero "
                        + "e-coordinate, while that cycle's indicator has "
                        + "e-coordinate one. The inclusion is therefore strict "
                        + "and the dimension strictly decreases. Dimension zero "
                        + "precludes a cycle, since any cycle has a nonzero edge "
                        + "indicator. The vertex type remains V throughout: "
                        + "isolated surviving vertices, and even the selected "
                        + "vertices now made isolated, remain present. No "
                        + "connectedness assumption is made on a residual graph.")),
                    Paragraph(Text(
                        "Once the residual graph is balanced, its unselected "
                        + "vertices send their potential bits. There is at most "
                        + "one selected x and at most one selected y in this "
                        + "construction. Each selected vertex sends its own "
                        + "special symbol, using alphabets mathbb B disjoint-union "
                        + "the selected singleton or empty set on the respective "
                        + "side. Two ordinary symbols decode by XOR. An Alice "
                        + "special symbol decodes to her original monochromatic "
                        + "bit; otherwise a Bob special symbol decodes to his "
                        + "bit. If both endpoints of a legal edge were selected, "
                        + "their original bits equal that edge's output, so "
                        + "the priority given to Alice is consistent. Distinct "
                        + "special bits cannot be joined by a legal edge. This "
                        + "defines actual total encoders and decoder with at "
                        + "most two ordinary symbols plus one selected symbol "
                        + "on each side.")),
                    Paragraph(Text(
                        "At rank zero the support is already balanced, giving "
                        + "(2,2). At rank at most one, one deletion on either "
                        + "specified side, if needed, leaves dimension zero "
                        + "and gives (3,2) or (2,3). At rank at most two, "
                        + "first select an Alice vertex on a nonzero-XOR cycle. "
                        + "If the residual graph is still unbalanced, select "
                        + "a Bob vertex on a residual nonzero-XOR cycle. Two "
                        + "strict dimension decreases leave dimension zero, "
                        + "giving (3,3). Together with the response-table "
                        + "endpoints and monotonicity of upper budgets, these "
                        + "protocols give every pair in the stated region.")),
                    Paragraph(Text(
                        "Necessity uses the following actual partial tables. "
                        + "Rows and columns are indexed from zero, and each "
                        + "star denotes an illegal pair, not an output.")),
                    Paragraph(Math(Examples())),
                    Paragraph(Text(
                        "F0 has three edges and four active vertices, connected "
                        + "support of rank zero, and one conflict edge on each "
                        + "side. Its entries at (0,0) and (1,0) force two Alice "
                        + "messages; those at (1,0) and (1,1) force two Bob "
                        + "messages. It belongs to every class under consideration, "
                        + "so p and q must both be at least two.")),
                    Paragraph(Text(
                        "F1 has six edges and six active vertices, connected "
                        + "support of rank one, and conflict colorings 010 and "
                        + "011. A (2,2) protocol would force equal Alice "
                        + "messages at rows 0 and 2 and equal Bob messages at "
                        + "columns 1 and 2. The legal pairs (0,2) and (2,1) "
                        + "would then have identical message pairs but outputs "
                        + "zero and one. Thus (2,2) is impossible at rank one.")),
                    Paragraph(Text(
                        "F2 has ten edges and nine active vertices. Its support "
                        + "is two four-cycles joined through row 4 and has rank "
                        + "two. Its conflict graphs are the paths 0-1-4-2-3 "
                        + "on rows and 0-1-2-3 on columns, with colorings "
                        + "01100 and 0101. With two Alice messages, the row "
                        + "classes are {0,3,4} and {1,2}; the four columns "
                        + "have respective responses 00,01,10,11, each "
                        + "coordinate determined by a legal pair. Equal Bob "
                        + "messages for any two columns would cause a legal "
                        + "output collision, so four Bob messages are required. "
                        + "With two Bob messages, the column classes are "
                        + "{0,2} and {1,3}; the five row responses are "
                        + "00,01,01,11,10. All four distinct responses occur, "
                        + "requiring four Alice messages. This excludes both "
                        + "(2,3) and (3,2). The finite-image equivalence makes "
                        + "these arguments apply to arbitrary message alphabets. "
                        + "Along with F0 and F1, they exclude every positive "
                        + "ordered pair outside the stated uniform region."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Card(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula App(Formula name, params Formula[] args) =>
        Seq(name, Open, Join(Comma, args), Close);
    private static Formula Join(Formula separator, params Formula[] values)
    {
        var items = new List<Formula>();
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, separator, Sp]);
            items.Add(values[i]);
        }
        return Seq([.. items]);
    }
    private static Formula Gather(params Formula[] rows) => Seq(
        Begin, Grp(V("gathered")), Join(RowBreak, rows), End, Grp(V("gathered")));
    private static Formula Matrix(params Formula[][] rows) => Seq(
        Begin, Grp(V("pmatrix")),
        Join(RowBreak, rows.Select(row => Join(Amp, row)).ToArray()),
        End, Grp(V("pmatrix")));

    private static Formula Rank() => Disp(Seq(
        V("mu"), Open, V("t"), Close, Sp, Eq, Sp,
        Card(App(V("D"), V("t"))), Sp, Plus, Sp, D(1), Sp,
        Minus, Sp, Card(V("X")), Sp, Minus, Sp, Card(V("Y")), Sp,
        Leq, Sp, V("s"), Comma, Sp,
        App(V("mu"), V("t")), Sp, InMacro, Sp, Mathbb, Grp(V("Z"))));

    private static Formula Statement()
    {
        var s = V("s"); var p = V("p"); var q = V("q");
        var hypotheses = Join(Land,
            Seq(s, Sp, Leq, Sp, D(2)),
            Seq(D(0), Sp, Lt, Sp, p),
            Seq(D(0), Sp, Lt, Sp, q));
        var region = Join(Land,
            Seq(D(2), Sp, Leq, Sp, p),
            Seq(D(2), Sp, Leq, Sp, q),
            Seq(s, Sp, Plus, Sp, D(4), Sp, Leq, Sp, p, Sp, Plus, Sp, q));
        return Disp(Seq(
            Forall, Sp, Join(Comma, s, p, q), Sp, InMacro, Sp,
            Mathbb, Grp(V("N")), Comma, Sp, Par(hypotheses), Sp, Implies, Sp,
            Par(Seq(App(V("UniformBudget"), s, p, q), Sp,
                Leftrightarrow, Sp, Par(region)))));
    }

    private static Formula Examples() => Disp(Gather(
        Seq(Sub(V("F"), D(0)), Sp, Eq, Sp, Matrix(
            [D(0), Star],
            [D(1), D(0)])),
        Seq(Sub(V("F"), D(1)), Sp, Eq, Sp, Matrix(
            [Star, Star, D(0)],
            [D(0), D(1), D(1)],
            [D(1), D(1), Star])),
        Seq(Sub(V("F"), D(2)), Sp, Eq, Sp, Matrix(
            [D(0), D(0), Star, Star],
            [D(0), D(1), Star, Star],
            [Star, Star, D(0), D(1)],
            [Star, Star, D(1), D(1)],
            [Star, D(0), D(1), Star]))));
}
