using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class LinearRadoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dimension inequalities yield spanning representatives and nonzero matrix minors.",
        H("Linear representative selection"),
        Blocks(
            Node("spanning_representatives", Spanning(),
                "The linear form of Rado's theorem selects one vector from each subspace. Its deficit version gives a spanning family: add an auxiliary space of dimension k − Module.finrank F W, choose independent representatives there, and project to W. The finite-set proof separates a proper set with equality in the dimension inequality; otherwise it passes to the quotient by a line.", false),
            Node("exists_nonsingular_rows", Minor(),
                "A finite family spanning a coordinate space contains a basis. Selecting its row indices gives a square submatrix with nonzero determinant.", true),
            Node("independent_support_matching", Matching(),
                "A linearly independent family of coordinate vectors has an injective selection of nonzero coordinates. A nonsingular maximal minor has a nonzero term in its determinant expansion, and the corresponding permutation supplies the selection.", true))));

    private static DocumentBlock Node(string name, Formula formula, string prose, bool derived) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/LinearRado." + name), H(name),
            StatementSource.FromAuthor(Disp(formula)),
            derived ? AssessedProvenance.FromRepo() : AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/FiniteGeometry/rado1942independence")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Spanning() => All("F", Type, Inst(A(V("Field"), V("F")),
        All("W", Type, Inst(A(V("AddCommGroup"), V("W")), Inst(A(V("Module"), V("F"), V("W")),
        Inst(A(V("FiniteDimensional"), V("F"), V("W")), All("k", N,
        All("L", Arrow(Fin(V("k")), Sub(V("F"), V("W"))),
        Imp(Rel(Rank(V("F"), V("W")), FormulaRelationOperator.LessThanOrEqual, V("k")),
        Imp(All("J", A(V("Finset"), Fin(V("k"))),
            Rel(Add(Rank(V("F"), V("W")), Card(V("J"))), FormulaRelationOperator.LessThanOrEqual,
                Add(V("k"), Rank(V("F"), A(V("iSup"), Lam("i",
                    A(V("Subtype"), Lam("j", Fin(V("k")), Member(V("j"), V("J")))),
                    A(V("L"), A(V("val"), V("i"))))))))),
        Some("l", Arrow(Fin(V("k")), V("W")),
            And(All("i", Fin(V("k")), Member(A(V("l"), V("i")), A(V("L"), V("i")))),
                Equal(A(Q("Submodule", "span"), V("F"), A(Q("Set", "range"), V("l"))), Q("Top", "top"))))))))))))));
    private static Formula Minor() => All("F", Type, Inst(A(V("Field"), V("F")),
        All("k", N, All("t", N, All("M", A(V("Matrix"), Fin(V("k")), Fin(V("t")), V("F")),
        Imp(Equal(A(Q("Submodule", "span"), V("F"), A(Q("Set", "range"), A(Q("Matrix", "row"), V("M")))), Q("Top", "top")),
        Some("f", Arrow(Fin(V("t")), Fin(V("k"))),
            And(A(Q("Function", "Injective"), V("f")),
                NotEqual(A(Q("Matrix", "det"), A(Q("Matrix", "submatrix"), V("M"), V("f"), V("id"))), new Formula.Number(0))))))))));
    private static Formula Matching() => All("K", Type, Inst(A(V("Field"), V("K")),
        All("i", Type, All("j", Type, Inst(A(V("Fintype"), V("i")), Inst(A(V("Fintype"), V("j")),
        All("v", Arrow(V("i"), Arrow(V("j"), V("K"))),
        Imp(A(V("LinearIndependent"), V("K"), V("v")),
        Some("f", Arrow(V("i"), V("j")),
            And(A(Q("Function", "Injective"), V("f")),
                All("a", V("i"), NotEqual(A(V("v"), V("a"), A(V("f"), V("a"))), new Formula.Number(0)))))))))))));
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
    private static Formula Fin(Formula n) => A(V("Fin"), n);
    private static Formula Sub(Formula f, Formula v) => A(V("Submodule"), f, v);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Member(Formula x, Formula s) => Rel(x, FormulaRelationOperator.MemberOf, s);
    private static Formula Card(Formula s) => A(Q("Finset", "card"), s);
    private static Formula Rank(Formula f, Formula u) => A(Q("Module", "finrank"), f, u);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
