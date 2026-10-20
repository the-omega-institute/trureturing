using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class LaPianaGraphQuantumMagicSquaresDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/LaPianaGraphQuantumMagicSquares";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/lapiana2025graphquantummagicsquares");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The C5 graph quantum magic squares strictly contain the matrix convex hull of graph quantum permutation matrices.",
        H("Graph quantum magic squares on C5"), Blocks(
            Node("qms", "IsQMS", QmsDefinition(), AssessedProvenance.FromLiterature(Source),
                "Definition 2.1, page 4: “A quantum magic square of external size n and internal size s is a block matrix” with “Aij ∈ Psds(ℂ),” “such that, for every i, j,” the displayed row and column sums equal Is. External indices use Fin n, internal indices use Fin s, and the identity is the matrix 1. The encoding includes the zero-size level, which consists of the unique empty matrices."),
            Node("graph-qms", "IsGraphQMS", GraphDefinition(), AssessedProvenance.FromLiterature(Source),
                "Definition 3.1, page 8: “A quantum magic square X = (Xij)1≤i,j≤n ∈ Matn(Hers(ℂ)) is called a graph quantum magic square if” X(Is ⊗ AΓ) = (Is ⊗ AΓ)X. “This commutation condition can be written in terms of internal blocks as” Σk∼j Xik = Σk∼i Xkj “∀ i, j ∈ {1, . . . , n},” “where k ∼ j means that vertices k and j are adjacent in Γ.” The formula uses exactly these block sums, with vertices indexed from zero."),
            Node("m", "M", MDefinition(), AssessedProvenance.FromLiterature(Source),
                "Definition 3.2, pages 8–9: “Let Γ be a finite graph with adjacency matrix AΓ, and let s ≥ 1. We define the following sets of graph quantum magic squares:” M^(Γ)s := { X ∈ M^(n)s | X(Is ⊗ AΓ) = (Is ⊗ AΓ)X }. The predicate IsGraphQMS spells out this condition blockwise. The natural-number levels also include size zero."),
            Node("p", "P", PDefinition(), AssessedProvenance.FromLiterature(Source),
                "Definition 3.2, page 9 defines P^(Γ)s := { X ∈ M^(Γ)s | Xij² = Xij = Xij* for all i, j }. Idempotence and conjugate-transpose symmetry are the two displayed conjuncts. The graph is a SimpleGraph on Fin n."),
            Node("matrix-convex", "IsMatrixConvex", MatrixConvexDefinition(), AssessedProvenance.FromLiterature(Source),
                "Definition 2.3, page 5: “We say that R is matrix convex if” the normalized blockwise sums displayed there belong to Rt. “Here the conjugation acts blockwise” and “Equivalently, we say that R is closed under matrix-valued convex combinations.” A finite family is indexed by Fin k; sz gives each input size, and V l has sz l rows and t columns. Conjugate transposes and products are matrix operations."),
            Node("hull", "mconv", HullDefinition(), AssessedProvenance.FromLiterature(Source),
                "Definition 2.3, page 5: “For a subset S ⊆ Matn(Hers(ℂ)), the matrix convex hull of S, denoted as mconv(S), is the smallest matrix convex set containing S.” The formula is membership in every matrix convex family containing S, at the same external size. It allows arbitrary finite input and output sizes."),
            Node("claim", "claim", Eqn(X("claim"), Parenthesized(ClaimBody())), AssessedProvenance.FromLiterature(Source),
                "Question 1.3, page 3: “Given a graph Γ, does the matrix convex hull of its quantum permutation matrices P^(Γ) generate all graph quantum magic squares? That is, mconv(P^(Γ)) = M^(Γ)?” Section 4.1, page 20: “A natural class of candidates is vertex-transitive or symmetric graphs, such as the cycle C5, the Petersen graph, and, more generally, any k-regular graph with a large automorphism group.” The displayed proposition answers the question for SimpleGraph.cycleGraph 5: containment holds at every internal size, and some level contains an element outside the hull."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + ".result"),
                H("Strict containment for C5"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Every graph quantum permutation matrix on C5 has commuting entries. Products of entries in its first two rows give positive families R and S with Xij = R(i−j) + S(i+j); the cycle recurrence extends this identity to all rows. This form is preserved by blockwise compression and finite sums. An internal-size-two graph quantum magic square has blocks (1/25) times [[5+a(i−j), b(i+j)], [b(i+j), 5−a(i−j)]], where a=(3,−3,0,0,0) and b=(4,−4,0,0,0). Four rank-one blocks force two R summands to vanish, contradicting their unequal top-left entries. Positivity and the row, column and graph relations are preserved by all normalized blockwise compressions, proving containment. Only C5 is asserted here."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("la-piana-2025-c5-graph-quantum-magic-squares"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock.Describe Node(string id, string name, Formula formula,
        AssessedProvenance provenance, string text) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Owner + "." + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula QmsDefinition() => All("n", Nat(), All("s", Nat(), All("A", BlocksType(X("n"), X("s")),
        Eqn(Call("IsQMS", X("A")), Parenthesized(And(
            All("i", Fin(X("n")), All("j", Fin(X("n")), Property(Call("A", X("i"), X("j")), "PosSemidef"))),
            And(All("i", Fin(X("n")), Eqn(Summation("k", Fin(X("n")), Call("A", X("i"), X("k"))), D(1))),
                All("j", Fin(X("n")), Eqn(Summation("k", Fin(X("n")), Call("A", X("k"), X("j"))), D(1))))))))));

    private static Formula GraphDefinition() => All("n", Nat(), All("s", Nat(), GraphBinders(
        All("X", BlocksType(X("n"), X("s")), Eqn(Call("IsGraphQMS", X("G"), X("X")),
            Parenthesized(And(Call("IsQMS", X("X")), All("i", Fin(X("n")), All("j", Fin(X("n")),
                Eqn(NeighborSum("j", Call("X", X("i"), X("k"))), NeighborSum("i", Call("X", X("k"), X("j")))))))))))));

    private static Formula MDefinition() => All("n", Nat(), GraphBinders(All("s", Nat(),
        Eqn(Call("M", X("G"), X("s")), SetBuilder("X", BlocksType(X("n"), X("s")), Call("IsGraphQMS", X("G"), X("X")))))));

    private static Formula PDefinition() => All("n", Nat(), GraphBinders(All("s", Nat(),
        Eqn(Call("P", X("G"), X("s")), SetBuilder("X", BlocksType(X("n"), X("s")),
            And(Call("IsGraphQMS", X("G"), X("X")), All("i", Fin(X("n")), All("j", Fin(X("n")),
                And(Eqn(Mul(Call("X", X("i"), X("j")), Call("X", X("i"), X("j"))), Call("X", X("i"), X("j"))),
                    Eqn(Adjoint(Call("X", X("i"), X("j"))), Call("X", X("i"), X("j"))))))))))));

    private static Formula MatrixConvexDefinition() => All("n", Nat(), All("R", Family(X("n")),
        Eqn(Call("IsMatrixConvex", X("R")), Parenthesized(All("k", Nat(),
            All("sz", Arrow(Fin(X("k")), Nat()), All("A", Pi("l", Fin(X("k")), BlocksType(X("n"), Call("sz", X("l")))),
                Imp(All("l", Fin(X("k")), Member(Call("A", X("l")), Call("R", Call("sz", X("l"))))),
                    All("t", Nat(), All("V", Pi("l", Fin(X("k")), Mat(Call("sz", X("l")), X("t"))),
                        Imp(Eqn(Summation("l", Fin(X("k")), Mul(Adjoint(Call("V", X("l"))), Call("V", X("l")))), D(1)),
                            Member(Parenthesized(Lambda("i", Fin(X("n")), Lambda("j", Fin(X("n")),
                                Summation("l", Fin(X("k")), Mul(Mul(Adjoint(Call("V", X("l"))), Call("A", X("l"), X("i"), X("j"))), Call("V", X("l"))))))), Call("R", X("t"))))))))))))));

    private static Formula HullDefinition() => All("n", Nat(), All("S", Family(X("n")), All("s", Nat(),
        Eqn(Call("mconv", X("S"), X("s")), SetBuilder("X", BlocksType(X("n"), X("s")),
            All("R", Family(X("n")), Imp(Call("IsMatrixConvex", X("R")),
                Imp(All("t", Nat(), Subset(Call("S", X("t")), Call("R", X("t")))), Member(X("X"), Call("R", X("s")))))))))));

    private static Formula ClaimBody()
    {
        var graph = App(Qualified("SimpleGraph", "cycleGraph"), D(5));
        var permutations = Call("P", graph);
        var magic = Call("M", graph, X("s"));
        var hull = Call("mconv", permutations, X("s"));
        return And(All("s", Nat(), Subset(hull, magic)), Ex("s", Nat(), Ex("X", BlocksType(D(5), X("s")),
            And(Member(X("X"), magic), Seq(Neg, Sp, Parenthesized(Member(X("X"), hull)))))));
    }

    private static Formula GraphBinders(Formula body) => All("G", App(X("SimpleGraph"), Fin(X("n"))),
        Seq(OpenBracket, Call("DecidableRel", App(Qualified("SimpleGraph", "Adj"), X("G"))), CloseBracket, Sp, Comma, Sp, body));
    private static Formula NeighborSum(string j, Formula body) => Seq(Sum, Sp, X("k"), Sp, InMacro, Sp,
        App(Qualified("Finset", "filter"), Parenthesized(Lambda("k", Fin(X("n")), App(Qualified("SimpleGraph", "Adj"), X("G"), X("k"), X(j)))), Qualified("Finset", "univ")), Sp, Comma, Sp, body);
    private static Formula Family(Formula n) => Pi("s", Nat(), App(X("Set"), BlocksType(n, X("s"))));
    private static Formula BlocksType(Formula n, Formula s) => Arrow(Fin(n), Arrow(Fin(n), Mat(s, s)));
    private static Formula Mat(Formula rows, Formula cols) => App(X("Matrix"), Fin(rows), Fin(cols), Complex());
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(X(name), args);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Pi(string name, Formula type, Formula body) => Seq(Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, To, Sp, body);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula type, Formula body) => Seq(X("fun"), Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Summation(string name, Formula type, Formula body) => Seq(Sum, Sp, X(name), Sp, Colon, Sp, type, Sp, Comma, Sp, body);
    private static Formula SetBuilder(string name, Formula type, Formula body) => Seq(OpenBrace, X(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Subset(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Property(Formula a, string name) => Seq(Parenthesized(a), Dot, Operatorname, Grp(X(name)));
    private static Formula Adjoint(Formula a) => App(Qualified("Matrix", "conjTranspose"), a);
}
