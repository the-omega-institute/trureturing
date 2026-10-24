using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class QuantumGraphStrangeComponentCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/GraphInvariants/spitzernechita2026quantumgraph");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantum graph components equal graph components plus loopless isolated strange edges.",
        H("The exact component count of a strange quantum graph"),
        Blocks(
            Paragraph(Text(
                "Write Mat n for D5.S3.Quantum.Matrix.CfmRadialDerivative.Mat n, the complex square matrices indexed by Fin n. "
                    + "Write offDiag for D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.offDiag, the complex linear map that sets the diagonal to zero. "
                    + "DFunLike.coe explicitly regards a linear map as a function. These notations give:")),
            new DocumentBlock.DisplayFormula(MatrixNotation()),
            new DocumentBlock.DisplayFormula(OffDiagonalNotation()),
            Node("realigned-projector", "realignedProjector", "The realigned block matrix",
                RealignedFormula(), AssessedProvenance.FromLiterature(Source),
                "The matrix has the scalar d i on the coordinate (i,i). On the two coordinates (i,j) and (j,i), for distinct i and j, "
                    + "its block has first row (A i j, C i j) and second row (C j i, A j i); all other entries vanish. "
                    + "This is the direct sum in content/groupactions.tex, lines 172–177, with the trivial middle matrix specified in lines 246–249. "
                    + "The definition itself allows arbitrary A, C and d; self-adjointness and idempotence are separate hypotheses."),
            Node("adjacency", "adjacency", "The adjacency operator by realignment",
                AdjacencyFormula(), AssessedProvenance.FromLiterature(Source),
                "Here MatrixMap.of_choi_matrix denotes D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_choi_matrix. "
                    + "Nested subscripts in the displayed declaration name encode underscores. "
                    + "It converts the displayed matrix into a complex linear adjacency operator. Writing X^R for realignedProjector A C d and G for adjacency A C d, "
                    + "the realignment formula is (GZ)_{ik} = ∑_{j,l} X^R_{(i,j),(k,l)} Z_{jl}. "
                    + "In particular, the output indices are the first and third indices of the realigned matrix. "
                    + "Realignment and its projector characterization appear in content/prelims.tex, lines 170–177."),
            new DocumentBlock.DisplayFormula(RealignmentFormula()),
            Node("has-components", "HasComponents", "A nonzero projection resolution",
                ComponentsFormula(), AssessedProvenance.FromLiterature(Source),
                "A family indexed by Fin k consists of nonzero self-adjoint idempotent matrices summing to the identity. "
                    + "For distinct s and t, left multiplication by P s annihilates G applied after left multiplication by P t, on every matrix Z. "
                    + "This expresses at least k quantum connected components, as in content/prelims.tex, lines 253–259; "
                    + "content/graphtheory/conncomp.tex, lines 1–4, makes the nonzero requirement explicit. "
                    + "The formulation includes k = 0 and n = 0."),
            Node("underlying-graph", "underlyingGraph", "The underlying simple graph",
                GraphFormula(), AssessedProvenance.FromLiterature(Source),
                "Two distinct vertices are adjacent exactly when at least one of the four entries of their off-diagonal block is nonzero. "
                    + "This relation is symmetric and excludes loops. Under the projector and undirectedness hypotheses, "
                    + "it forgets the edge types and phases of the strange graph in content/groupactions.tex, lines 408–427. "
                    + "Without those hypotheses it still defines the simple support graph of the four entries."),
            Node("loop-free-strange-component", "IsLoopFreeStrangeComponent", "An isolated strange edge without endpoint loops",
                ExceptionalFormula(), AssessedProvenance.FromRepo(Source),
                "This predicate is introduced here to state the exact component count. "
                    + "The support of Q must consist of exactly two distinct adjacent vertices i and j, with A i j = 1/2 and d i = d j = 0. "
                    + "Under the projector and undirectedness hypotheses, A i j = 1/2 identifies a strange edge, "
                    + "whose conjugate off-diagonal coefficients have product 1/4. The predicate places no restriction on its phase. "
                    + "It is a condition on a whole connected component, so the edge is isolated from all other vertices."),
            Node("graph-component-count", "graphComponentCount", "The classical component count",
                GraphCountFormula(), AssessedProvenance.FromLiterature(Source),
                "This natural number is the cardinality of the connected-component type of the underlying simple graph, including isolated vertices. "
                    + "It is the classical count compared with the quantum count in content/graphtheory/conncomp.tex, lines 196–213 and 247–254. "
                    + "The cardinality is already a natural number; no scalar conversion is involved."),
            Node("loop-free-strange-component-count", "loopFreeStrangeComponentCount", "The exceptional component count",
                ExceptionalCountFormula(), AssessedProvenance.FromRepo(Source),
                "This natural number is introduced here to state the exact component count. "
                    + "It counts precisely the connected components satisfying IsLoopFreeStrangeComponent. "
                    + "Each unordered two-vertex component is counted once, independently of the choice of its two endpoints. "
                    + "The subtype cardinality is a natural number, with no scalar conversion."),
            Node("claim", "claim", "The exact-count assertion",
                Equivalent(Name("claim"), ClaimFormula()), AssessedProvenance.FromRepo(Source),
                "The common diagonal conditions are A i i = d i and C i i = d i for every i. "
                    + "The realigned matrix is self-adjoint and idempotent, and offDiag A is self-adjoint. "
                    + "For every natural size n, the assertion says that the sum of the two displayed natural counts is both attainable "
                    + "as a quantum component count and an upper bound for all attainable counts. "
                    + "The question in content/conclusion.tex, line 8, asks for the exact count and the role of isolated strange edges of phase π; "
                    + "it does not give this formula. The asserted answer adds one for every isolated strange edge with zero endpoint diagonals, of any phase."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The greatest attainable quantum component count"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                ResultArgument(),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("spitzer-nechita-2026-quantum-graph-component-count"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static BlockSequence ResultArgument() => Blocks(
        Paragraph(Text(
            "Fix n, A, C and d satisfying the five hypotheses. First examine a block indexed by distinct i and j. "
                + "Self-adjointness gives A j i = A i j, conjugate(A i j) = A i j and C j i = conjugate(C i j). "
                + "Idempotence gives (A i j)² + (C i j)(C j i) = A i j and (A i j)(C i j) + (C i j)(A j i) = C i j. "
                + "Thus the block is zero, the identity, or a strange block with A i j = A j i = 1/2 and (C i j)(C j i) = 1/4. "
                + "In particular A i j is nonzero on every edge.")),
        Paragraph(Text(
            "For each pair q let K_q be the matrix whose (i,j) entry is X^R_{(i,j),q}. "
                + "The diagonal matrices are K_(i,i) = d i E_ii, and for distinct i,j one has K_(i,j) = (A i j)E_ij + (C j i)E_ji. "
                + "Commutation of a matrix P with every K_q forces P i i = P j j along each edge, hence along every path. "
                + "For an edge i–j and a third vertex r, the same equations force P r i = 0. "
                + "For distinct i and j they also give (P i j)(A j i) = (C i j)(P j i), and a nonzero P i j forces d i = d j = 0. "
                + "If P is self-adjoint, i ≠ j, i has a neighbor and P i j is nonzero, then j is the only neighbor of i and i is the only neighbor of j. "
                + "Their connected component is exactly {i,j}; the identity-block case would force P i j = 0, "
                + "so this component is a loop-free isolated strange edge.")),
        Paragraph(Text(
            "The projector identity for X^R yields G(Z) = ∑_q K_q Z K_qᴴ: the Choi matrix of this sum has entries "
                + "∑_r X^R_{p,r} conjugate(X^R_{q,r}) = X^R_{p,q}. "
                + "A sum of matrices T_r T_rᴴ can vanish only when every T_r vanishes, since all its summands are positive semidefinite. "
                + "Applying this fact to a projection resolution of the identity proves that its distinct members are orthogonal. "
                + "For two self-adjoint projections P and Q, the identity P G(QZ) = 0 for every Z is equivalent to P K_q Q = 0 for every q: "
                + "take Z = I, multiply on the right by P, and use the vanishing positive sum. "
                + "Summing the cross terms against a resolution of I now shows that the separation conditions are equivalent "
                + "to every projection commuting with every K_q. Orthogonality proves the converse.")),
        Paragraph(Text(
            "To bound such a resolution, form W as the disjoint union of all connected components and the subtype of loop-free isolated strange components. "
                + "Select one representative vertex of every component, and also the other vertex of each component in the subtype. "
                + "These selected vertices are distinct, and |W| is graphComponentCount A C + loopFreeStrangeComponentCount A C d. "
                + "They include every isolated vertex and both endpoints of every exceptional edge. Every omitted vertex therefore has a neighbor "
                + "and belongs to a nonexceptional component. The preceding commutation equations force all off-diagonal entries "
                + "incident to that vertex to vanish for every self-adjoint matrix in the commutant.")),
        Paragraph(Text(
            "Compress each member P s of a resolution to the selected coordinates. The vanished entries show that compression preserves its square, "
                + "so each compressed matrix is idempotent. It is nonzero: if it vanished, constancy of the diagonal on connected components "
                + "would also kill every omitted diagonal entry, and the vanished off-diagonal entries would give P s = 0. "
                + "The compressed matrices sum to the identity on the coordinate space W → ℂ. "
                + "The bound for a sum of nonzero idempotent endomorphisms, D5.S3.Quantum.Matrix.RecordCapacity.card_le_finrank_of_idempotent_sum, "
                + "therefore gives k ≤ dimℂ(W → ℂ) = |W|, which is the required upper bound.")),
        Paragraph(Text(
            "For attainment, take the diagonal projection D_Q onto each connected component Q. "
                + "These are nonzero self-adjoint projections summing to I and commuting with all K_q. "
                + "Matrices K_(i,j) between different components vanish. On an exceptional component {i,j}, put b = C j i. "
                + "The block equations give b conjugate(b) = 1/4. Algebraic closedness of ℂ supplies z with z² = 2b. "
                + "Then (z conjugate(z))² = 1, and nonnegativity excludes the value −1, so z conjugate(z) = 1. "
                + "Set D = E_ii + E_jj and H = conjugate(z)E_ij + z E_ji. "
                + "Direct multiplication gives D² = D, DH = HD = H and H² = D; H is self-adjoint. "
                + "Hence P = (D + H)/2 and R = D − P are nonzero self-adjoint projections, each with diagonal entries 1/2 at i and j, and P + R = D.")),
        Paragraph(Text(
            "Here K_(i,j) = (z/2)H and K_(j,i) = K_(i,j)ᴴ, so P commutes with both. "
                + "The two diagonal matrices K_(i,i) and K_(j,j) vanish because d i = d j = 0. "
                + "Matrices between this pair and its complement vanish, while those supported in the complement multiply P to zero on either side. "
                + "Thus P commutes with every K_q, and R does too, by subtracting P from D_Q. "
                + "Replace D_Q by P and R on each exceptional component and retain D_Q on every other component. "
                + "Indexing this family by W gives exactly graphComponentCount A C + loopFreeStrangeComponentCount A C d nonzero projections, "
                + "still commuting with every K_q and still summing to I. Reindex by Fin of this natural number and use the separation equivalence "
                + "to obtain an attainable quantum component count. Together with the upper bound, this proves it is the greatest attainable count. "
                + "The construction uses no special phase, so every isolated strange edge with zero endpoint diagonals contributes two components, "
                + "and every other graph component contributes one. If d vanishes everywhere, the correction counts all isolated strange edges.")));

    private static Formula MatrixNotation() => All("n", Naturals(),
        Equal(Mat(), App(Name("Matrix"), FinOf(X("n")), FinOf(X("n")), Complexes())));

    private static Formula OffDiagonalNotation() => All("d", Naturals(), All("X", MatOf(X("d")),
        All("i", FinOf(X("d")), All("j", FinOf(X("d")),
            Equal(App(CoerceFunction(Name("offDiag")), X("X"), X("i"), X("j")),
                If(Equal(X("i"), X("j")), ComplexNumber(0), App(X("X"), X("i"), X("j"))))))));

    private static Formula RealignedFormula()
    {
        Formula p1 = Projection(X("p"), 1);
        Formula p2 = Projection(X("p"), 2);
        Formula diagonal = If(Equal(X("q"), Pair(p1, p1)), App(X("d"), p1), ComplexNumber(0));
        Formula off = If(Equal(X("q"), X("p")), App(X("A"), p1, p2),
            If(Equal(X("q"), Pair(p2, p1)), App(X("C"), p1, p2), ComplexNumber(0)));
        return Parameters(All("p", PairType(), All("q", PairType(),
            Equal(App(Realigned(), X("p"), X("q")), If(Equal(p1, p2), diagonal, off)))));
    }

    private static Formula AdjacencyFormula() => Parameters(
        Equal(Typed(Adjacency(), LinearEnd()), App(Qualified("MatrixMap", "of_choi_matrix"), Realigned())));

    private static Formula RealignmentFormula()
    {
        Formula summand = Multiply(App(Realigned(), Pair(X("i"), X("j")), Pair(X("k"), X("l"))),
            App(X("Z"), X("j"), X("l")));
        Formula sum = SumOver("j", FinOf(X("n")), SumOver("l", FinOf(X("n")), summand));
        Formula entry = App(CoerceFunction(Adjacency()), X("Z"), X("i"), X("k"));
        return Parameters(All("Z", Mat(), All("i", FinOf(X("n")), All("k", FinOf(X("n")), Equal(entry, sum)))));
    }

    private static Formula ComponentsFormula()
    {
        Formula ps = App(X("P"), X("s"));
        Formula pt = App(X("P"), X("t"));
        Formula projections = All("s", FinOf(X("k")),
            And(App(Name("IsStarProjection"), ps), NotEqual(ps, MatrixNumber(0))));
        Formula complete = Equal(SumOver("s", FinOf(X("k")), ps), MatrixNumber(1));
        Formula separate = All("s", FinOf(X("k")), All("t", FinOf(X("k")),
            ImpliesFormula(NotEqual(X("s"), X("t")), All("Z", Mat(),
                Equal(Multiply(ps, App(CoerceFunction(X("G")), Multiply(pt, X("Z")))), MatrixNumber(0))))));
        return All("n", Naturals(), All("G", LinearEnd(), All("k", Naturals(),
            Equivalent(App(Name("HasComponents"), X("G"), X("k")),
                Some("P", Arrow(FinOf(X("k")), Mat()), And(projections, And(complete, separate)))))));
    }

    private static Formula GraphFormula()
    {
        Formula nonzero = Or(NotEqual(App(X("A"), X("i"), X("j")), ComplexNumber(0)),
            Or(NotEqual(App(X("A"), X("j"), X("i")), ComplexNumber(0)),
                Or(NotEqual(App(X("C"), X("i"), X("j")), ComplexNumber(0)),
                    NotEqual(App(X("C"), X("j"), X("i")), ComplexNumber(0)))));
        return MatrixParameters(All("i", FinOf(X("n")), All("j", FinOf(X("n")),
            Equivalent(Adjacent(), And(NotEqual(X("i"), X("j")), nonzero)))));
    }

    private static Formula ExceptionalFormula()
    {
        Formula loops = And(Equal(App(X("d"), X("i")), ComplexNumber(0)),
            Equal(App(X("d"), X("j")), ComplexNumber(0)));
        Formula half = Equal(App(X("A"), X("i"), X("j")),
            new Formula.Fraction(ComplexNumber(1), ComplexNumber(2)));
        Formula support = Equal(App(Qualified("SimpleGraph", "ConnectedComponent", "supp"), X("Q")),
            new Formula.SetLiteral([X("i"), X("j")]));
        Formula pair = And(NotEqual(X("i"), X("j")), And(support, And(Adjacent(), And(half, loops))));
        return Parameters(All("Q", Components(), Equivalent(Exceptional(),
            Some("i", FinOf(X("n")), Some("j", FinOf(X("n")), pair)))));
    }

    private static Formula GraphCountFormula() => MatrixParameters(
        Equal(Typed(App(Name("graphComponentCount"), X("A"), X("C")), Naturals()),
            App(Qualified("Fintype", "card"), Components())));

    private static Formula ExceptionalCountFormula() => Parameters(
        Equal(Typed(App(Name("loopFreeStrangeComponentCount"), X("A"), X("C"), X("d")), Naturals()),
            App(Qualified("Fintype", "card"), Seq(OpenBrace, X("Q"), Colon, Sp, Components(), Sp, Slash, Slash, Sp,
                Exceptional(), CloseBrace))));

    private static Formula ClaimFormula()
    {
        Formula set = Seq(OpenBrace, Typed(X("k"), Naturals()), Sp, Mid, Sp,
            App(Name("HasComponents"), Adjacency(), X("k")), CloseBrace);
        Formula count = Add(App(Name("graphComponentCount"), X("A"), X("C")),
            App(Name("loopFreeStrangeComponentCount"), X("A"), X("C"), X("d")));
        Formula greatest = App(Name("IsGreatest"), set, count);
        Formula offDiagonal = App(Name("IsHermitian"), App(CoerceFunction(Name("offDiag")), X("A")));
        return Parameters(ImpliesFormula(All("i", FinOf(X("n")), Equal(App(X("A"), X("i"), X("i")), App(X("d"), X("i")))),
            ImpliesFormula(All("i", FinOf(X("n")), Equal(App(X("C"), X("i"), X("i")), App(X("d"), X("i")))),
                ImpliesFormula(App(Name("IsHermitian"), Realigned()),
                    ImpliesFormula(Equal(Multiply(Realigned(), Realigned()), Realigned()),
                        ImpliesFormula(offDiagonal, greatest))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string first, string second) =>
        Seq(Operatorname, Grp(F.Id(first), Dot, Identifier(second)));
    private static Formula Qualified(string first, string second, string third) =>
        Seq(Operatorname, Grp(F.Id(first), Dot, F.Id(second), Dot, F.Id(third)));
    private static Formula Identifier(string name)
    {
        var parts = name.Split('_');
        Formula value = F.Id(parts[^1]);
        for (var i = parts.Length - 2; i >= 0; --i)
            value = Seq(F.Id(parts[i]), Underscore, Grp(value));
        return value;
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula CoerceFunction(Formula value) => App(Qualified("DFunLike", "coe"), value);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => App(Name("Fin"), size);
    private static Formula MatOf(Formula size) => App(Name("Mat"), size);
    private static Formula Mat() => MatOf(X("n"));
    private static Formula PairType() => Seq(FinOf(X("n")), Sp, Times, Sp, FinOf(X("n")));
    private static Formula LinearEnd() => Seq(Parenthesized(Mat()), Sp,
        new Formula.Subscript(To, Seq(F.Id("l"), OpenBracket, Complexes(), CloseBracket)), Sp, Parenthesized(Mat()));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula ComplexNumber(byte value) => Typed(D(value), Complexes());
    private static Formula MatrixNumber(byte value) => Typed(D(value), Mat());
    private static Formula Realigned() => App(Name("realignedProjector"), X("A"), X("C"), X("d"));
    private static Formula Adjacency() => App(Name("adjacency"), X("A"), X("C"), X("d"));
    private static Formula Graph() => App(Name("underlyingGraph"), X("A"), X("C"));
    private static Formula Components() => App(Qualified("SimpleGraph", "ConnectedComponent"), Graph());
    private static Formula Exceptional() => App(Name("IsLoopFreeStrangeComponent"), X("A"), X("C"), X("d"), X("Q"));
    private static Formula Adjacent() => App(Qualified("SimpleGraph", "Adj"), Graph(), X("i"), X("j"));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Projection(Formula value, byte field) => Seq(Parenthesized(value), Dot, D(field));
    private static Formula If(Formula condition, Formula yes, Formula no) => App(Name("ite"), Parenthesized(condition), yes, no);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula MatrixParameters(Formula body) =>
        All("n", Naturals(), All("A", Mat(), All("C", Mat(), body)));
    private static Formula Parameters(Formula body) => MatrixParameters(All("d", Arrow(FinOf(X("n")), Complexes()), body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
}
