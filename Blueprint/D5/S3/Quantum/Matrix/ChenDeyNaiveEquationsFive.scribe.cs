using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ChenDeyNaiveEquationsFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/ChenDeyNaiveEquationsFive.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/chendey2023orthostochastic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The naive orthostochastic equations are insufficient at order five.",
        H("Pairwise signs do not give an orthogonal lift at order five"), Blocks(
            Paragraph(Text("Indices belong to Fin n and start at zero. Every sum over Fin n includes all n indices. "
                + "The source numbers indices from one. Signs are real numbers equal to 1 or −1. Allowing a sign on every term gives the same zero-sum condition as fixing the first sign to 1, since all signs may be reversed together. "
                + "The Birkhoff polytope is Mathlib's doublyStochastic set.")),
            Entry("orthostochastic", "IsOrthostochastic", "Orthostochastic matrices", OrthostochasticFormula(),
                "Section 1, page 1: \"A real square matrix is called orthostochastic if it is the entrywise square of an orthogonal matrix.\" For real U, RHLinalg.normSqMatrix U has entry ‖U i j‖² = (U i j)².",
                AssessedProvenance.FromLiterature(Source)),
            Entry("columns", "ColumnNaive", "The column naive equation", NaiveFormula(false),
                "After Definition 4, page 4: \"a doubly stochastic matrix A satisfies C_{i,j} = 0 if and only if there exist choices of signs ε_1, …, ε_{n−1} such that with these choices of signs, the entrywise square roots of the i-th and j-th columns of A become orthogonal.\" The formula writes this sign condition; its application in claim assumes that the matrix is doubly stochastic.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("rows", "RowNaive", "The row naive equation", NaiveFormula(true),
                "Definition 4, page 3, defines the row equations \"by transposing indices\". RowNaive is the same sign condition with the row and column indices exchanged.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("all-equations", "SatisfiesNaive", "All row and column naive equations", SatisfiesFormula(),
                "Definition 4, page 3, calls these the \"naive equations\" and counts n(n−1) equations in total. The formula requires both conditions for each i < j.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("matrix", "B", "The positive five by five matrix", MatrixFormula(),
                "The matrix is (4J−3I)/17, with diagonal entries 1/17 and off-diagonal entries 4/17. The typed 1 supplied to Matrix.of is the constant function of two Fin 5 arguments with value 1, written fun _ _ => (1 : ℝ) in Lean. Every row and column sums to 1.",
                AssessedProvenance.FromRepo(Source)),
            Entry("question", "claim", "Question 5 at order five", ClaimFormula(),
                "Question 5, page 4: \"Do the naive equations define the orthostochastic variety inside B_n? In other words, if a doubly stochastic matrix satisfies C_{i,j}, R_{i,j} = 0 for all i < j, must it be orthostochastic?\" Section 5, page 7: \"Next, for n = 4, 5 it remains open whether the naive equations cut out the orthostochastic variety inside the Birkhoff polytope set-theoretically.\" The formula is the n = 5 clause: the matrix ranges over all real five by five matrices and the lift over all real orthogonal matrices.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A negative answer at order five", Disp(Seq(Neg, Sp, V("claim"))),
                "For any two distinct columns of B, the five radical terms are 2/17, 2/17, 4/17, 4/17 and 4/17. Taking positive signs on the two distinguished positions and on one other position gives zero. Symmetry gives the row conditions. "
                + "If B had a real orthogonal lift U, the matrix √17 U would have integer entries: ±1 on the diagonal and ±2 elsewhere. Its product with its transpose would be 17I, so its integer determinant would have square 17⁵. The latter is not a square. "
                + "This answers the order-five clause negatively. The order-four clause remains open; the source's Proposition 6 already gives a negative answer for every n ≥ 6.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("chen-dey-2020-orthostochastic-naive-equations-five"),
                ResolutionKind.Refuted) : null);

    private static Formula OrthostochasticFormula()
    {
        Formula n = V("n"), b = V("B"), u = V("U");
        return Disp(All("n", Nat(), All("B", Matrix(n),
            Equal(Call("IsOrthostochastic", b), ExistsIn("U", Matrix(n),
                And(Member(u, App(Qualified("Matrix", "orthogonalGroup"), Fin(n), Real())),
                    Equal(b, App(Qualified("RHLinalg", "normSqMatrix"), u))))))));
    }

    private static Formula NaiveFormula(bool rows)
    {
        Formula n = V("n"), b = V("B"), i = V("i"), j = V("j"), k = V("k"), e = V("e");
        Formula signs = All("k", Fin(n), Or(Equal(App(e, k), D(1)), Equal(App(e, k), Negative(D(1)))));
        Formula product = rows ? Multiply(App(b, i, k), App(b, j, k))
            : Multiply(App(b, k, i), App(b, k, j));
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Colon, Sp, Fin(n))), Sp,
            Multiply(App(e, k), App(Qualified("Real", "sqrt"), product)));
        return Disp(All("n", Nat(), All("B", Matrix(n), All("i", Fin(n), All("j", Fin(n),
            Equal(Call(rows ? "RowNaive" : "ColumnNaive", b, i, j),
                ExistsIn("e", Arrow(Fin(n), Real()), And(signs, Equal(sum, D(0))))))))));
    }

    private static Formula SatisfiesFormula()
    {
        Formula n = V("n"), b = V("B"), i = V("i"), j = V("j");
        return Disp(All("n", Nat(), All("B", Matrix(n), Equal(Call("SatisfiesNaive", b),
            All("i", Fin(n), All("j", Fin(n), Imp(
                new Formula.Relation(i, FormulaRelationOperator.LessThan, j),
                And(Call("ColumnNaive", b, i, j), Call("RowNaive", b, i, j)))))))));
    }

    private static Formula MatrixFormula()
    {
        Formula one = Parenthesized(Seq(D(1), Colon, Sp, Matrix(D(5))));
        Formula constant = Parenthesized(Seq(D(1), Colon, Sp, Arrow(Fin(D(5)), Arrow(Fin(D(5)), Real()))));
        return Disp(Equal(V("B"), Smul(new Formula.Fraction(D(1), D(1, 7)), Parenthesized(
            Subtract(Smul(D(4), App(Qualified("Matrix", "of"), constant)), Smul(D(3), one))))));
    }

    private static Formula ClaimFormula()
    {
        Formula b = V("B");
        return Disp(Equal(V("claim"), All("B", Matrix(D(5)),
            Imp(Member(b, App(V("doublyStochastic"), Real(), Fin(D(5)))),
                Imp(Call("SatisfiesNaive", b), Call("IsOrthostochastic", b))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula n) => Call("Matrix", Fin(n), Fin(n), Real());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Negative(Formula a) => Seq(Minus, a);
    private static Formula Smul(Formula a, Formula b) => App(Qualified("HSMul", "hSMul"), a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
