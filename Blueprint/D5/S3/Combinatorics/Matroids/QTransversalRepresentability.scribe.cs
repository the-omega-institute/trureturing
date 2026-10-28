using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class QTransversalRepresentabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every q-transversal rank function has a representation over a finite field extension.",
        H("Q-transversal representability"),
        Blocks(
            Node("IsPartialQTransversal", PartialDefinition(),
                "Definition 14, page 8: “Let a vector space V be given, together with a family X = (X₁, …, X_n) of subspaces of V.” “A partial q-transversal is a dimension n subspace T where every vector basis of T is a partial avoiding transversal of X.” Here the family has k indices and the ambient space is Fin m → F. As in Theorems 15 and 18, partial q-transversals may have any dimension. A vector basis is a finite linearly independent set spanning T, and an avoiding injection sends each basis vector to an index of a subspace not containing it.", DescribeRole.Definition, false),
            Node("qTransversalRank", RankDefinition(),
                "Theorem 15, page 8: “Given a family X = (X_i : i ∈ I) where each X_i is a subspace of V, the set of partial q-transversals of X form the independent subspaces of a q-matroid.” The rank of U is the supremum of the dimensions of partial q-transversals contained in U. The set of dimensions is nonempty and bounded by Module.finrank F U.", DescribeRole.Definition, false),
            Node("representedRank", RepresentedDefinition(),
                "Section 3.2, page 7: “Given some n × m matrix G over a field K extending F_q, we can define the q-matroid represented by G as follows: if a subspace of F_q^m is the row space of matrix X, then its rank in the matroid is the rank of matrix G Xᵀ.” The columns of the second factor are the vectors of Module.finBasis F U, with each coordinate mapped to K by algebraMap. This is the transpose of the matrix whose rows form that basis.", DescribeRole.Definition, false),
            Node("claim", IffFormula(V("claim"), ClaimBody()),
                "Section 4.2, page 14: “Conjecture 3. All q-transversal matroids are representable.” The field F is arbitrary and finite, X is an arbitrary finite family of subspaces, and the same G represents the ranks of every U. The field extension K is finite dimensional over F.", DescribeRole.Definition, false),
            Node("result", ClaimBody(),
                "One finite extension preserves a nonzero generic minor for every partial q-transversal. The rows are functionals vanishing on the corresponding subspaces. A determinant support matching gives the converse implication, and independent columns yield a subspace attaining the represented rank. Consequently the two rank functions agree on every subspace. The proof gives a finite extension; no sharp formula for its degree is asserted.", DescribeRole.Theorem, true))));

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, bool derived) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/QTransversalRepresentability." + name),
            H(name), StatementSource.FromAuthor(Disp(formula)),
            derived ? AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGeometry/saaltink2025qtransversals"))
                : AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGeometry/saaltink2025qtransversals")),
            Blocks(Paragraph(Text(prose))), role,
            null);

    private static Formula Ambient => Arrow(Fin(V("m")), V("F"));
    private static Formula Family => Arrow(Fin(V("k")), Sub(V("F"), Ambient));
    private static Formula Base(Formula body, bool finite = false) => All("F", Type,
        Inst(A(V("Field"), V("F")), finite
            ? Inst(A(V("Fintype"), V("F")), All("m", N, All("k", N, All("X", Family, body))))
            : All("m", N, All("k", N, All("X", Family, body)))));
    private static Formula PartialDefinition() => Base(All("T", Sub(V("F"), Ambient),
        IffFormula(A(V("IsPartialQTransversal"), V("X"), V("T")),
            All("s", A(V("Finset"), Ambient),
                Imp(A(V("LinearIndependent"), V("F"), Lam("b", V("s"), Coe(V("b"), Ambient))),
                Imp(Equal(A(Q("Submodule", "span"), V("F"), Coe(V("s"), A(V("Set"), Ambient))), V("T")),
                    Some("f", Arrow(V("s"), Fin(V("k"))),
                        And(A(Q("Function", "Injective"), V("f")),
                            All("b", V("s"), NotMember(Coe(V("b"), Ambient), A(V("X"), A(V("f"), V("b")))))))))))));
    private static Formula RankDefinition() => Base(All("U", Sub(V("F"), Ambient),
        Equal(A(V("qTransversalRank"), V("X"), V("U")),
            A(V("sSup"), Seq(OpenBrace, V("d"), Sp, Mid, Sp,
                Some("T", Sub(V("F"), Ambient),
                    And(Rel(V("T"), FormulaRelationOperator.LessThanOrEqual, V("U")),
                        And(A(V("IsPartialQTransversal"), V("X"), V("T")), Equal(Rank(V("F"), V("T")), V("d"))))), CloseBrace)))));
    private static Formula RepresentedDefinition() => All("F", Type,
        Inst(A(V("Field"), V("F")),
        All("K", Type, Inst(A(V("Field"), V("K")), Inst(A(V("Algebra"), V("F"), V("K")),
        All("r", N, All("m", N, All("G", A(V("Matrix"), Fin(V("r")), Fin(V("m")), V("K")),
        All("U", Sub(V("F"), Ambient), Equal(A(V("representedRank"), V("G"), V("U")),
            A(Q("Matrix", "rank"), Multiply(V("G"),
                A(Q("Matrix", "of"), Lam("j", Fin(V("m")), Lam("i", Fin(Rank(V("F"), V("U"))),
                    A(A(V("algebraMap"), V("F"), V("K")),
                        A(Coe(A(Q("Module", "finBasis"), V("F"), V("U"), V("i")), Ambient), V("j"))))))))))))))))));
    private static Formula ClaimBody() => Base(Some("K", Type,
        Inst(A(V("Field"), V("K")), Inst(A(V("Algebra"), V("F"), V("K")),
        Inst(A(V("FiniteDimensional"), V("F"), V("K")),
        Some("r", N, Some("G", A(V("Matrix"), Fin(V("r")), Fin(V("m")), V("K")),
        All("U", Sub(V("F"), Ambient), Equal(A(V("representedRank"), V("G"), V("U")),
            A(V("qTransversalRank"), V("X"), V("U")))))))))), true);
    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Type => V("Type");
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula A(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Fin(Formula n) => A(V("Fin"), n);
    private static Formula Sub(Formula f, Formula v) => A(V("Submodule"), f, v);
    private static Formula Coe(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Member(Formula x, Formula s) => Rel(x, FormulaRelationOperator.MemberOf, s);
    private static Formula NotMember(Formula x, Formula s) => Seq(Neg, Sp, Parenthesized(Member(x, s)));
    private static Formula Rank(Formula f, Formula u) => A(Q("Module", "finrank"), f, u);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
