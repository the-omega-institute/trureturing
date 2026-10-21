using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ZhangJingBlockNormalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/zhangjing2025positive");

    private const string Question = "Let A ∈ M_n. Then [[f(|A|), A*], [A, g(|A|)]] ≥ 0 if and only "
        + "if A is normal under the conditions that f(x)g(x) = x² for x ≥ 0, f(x) ≥ g(x) (x ≥ 1) "
        + "and g(x) ≥ f(x) (0 ≤ x ≤ 1).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An admissible scalar pair gives a positive block for a nonnormal complex matrix.",
        H("A positive block does not force normality"),
        Blocks(
            Entry("zhang-jing-block", "block", "The source block matrix", BlockFormula(),
                "The source defines ‘|A| = (A*A)^{1/2} and A* is the conjugate transpose of A’ "
                + "(p. 595). Question 2.14 (p. 601) states: “" + Question + "” "
                + "Here Matrix.conjTranspose is A*, and CFC.sqrt gives the positive square root "
                + "of A* A. The real functions are applied by cfc. Matrix.fromBlocks places "
                + "these four blocks in the displayed order; its index type is Fin n ⊕ Fin n.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("zhang-jing-claim", "claim", "Question 2.14 as a universal equivalence",
                Disp(Iff(V("claim"), ClaimBody())),
                "Question 2.14 (p. 601): “" + Question + "” "
                + "The proposition quantifies over every pair of real functions f,g satisfying "
                + "the three scalar conditions, every natural dimension n, and every complex "
                + "matrix on Fin n. Nonnegativity of the block is Matrix.PosSemidef, and "
                + "normality is the equality of A* A and A A*. Fin n labels the source's n indices "
                + "from zero. No continuity, invertibility or spectral injectivity hypothesis is added.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("zhang-jing-result", "result", "The universal equivalence is false",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "Set g(x)=1+(x−1)/(1+(x−1)²) and f(x)=x²/g(x). The denominator is positive, "
                + "g is positive on the real line, and the three scalar conditions hold on their "
                + "respective ranges. Take A=[[0,3/2],[3,0]]. Then |A|=diag(3,3/2), "
                + "f(|A|)=diag(45/7,45/28), and g(|A|)=(7/5)I: the distinct singular values "
                + "3 and 3/2 have the same value under g. For the block row Q=[A,(7/5)I], "
                + "the block equals (5/7)Q*Q and is positive semidefinite. However, the (0,0) "
                + "entries of A* A and A A* are 9 and 9/4, so A is not normal. "
                + "The refutation uses this fixed two-dimensional example; no general injectivity "
                + "criterion or classification of singular matrices is asserted. In this pair "
                + "f(0)=0; strict positivity of f holds only for x>0.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula BlockFormula()
    {
        Formula n = V("n"), f = V("f"), g = V("g"), a = V("A");
        Formula modulus = Call("CFC.sqrt", Mul(Call("Matrix.conjTranspose", a), a));
        Formula body = Call("Matrix.fromBlocks", Call("cfc", f, modulus),
            Call("Matrix.conjTranspose", a), a, Call("cfc", g, modulus));
        return Disp(All("f", RealFunction(), All("g", RealFunction(), All("n", Nat(),
            All("A", Matrix(n), Equal(Call("block", f, g, a), body))))));
    }

    private static Formula ClaimBody()
    {
        Formula f = V("f"), g = V("g"), x = V("x"), n = V("n"), a = V("A");
        Formula product = All("x", Real(), Imp(Leq(D(0), x),
            Equal(Mul(App(f, x), App(g, x)), new Formula.Power(x, D(2)))));
        Formula high = All("x", Real(), Imp(Leq(D(1), x), Leq(App(g, x), App(f, x))));
        Formula low = All("x", Real(), Imp(Leq(D(0), x),
            Imp(Leq(x, D(1)), Leq(App(f, x), App(g, x)))));
        Formula normal = Equal(Mul(Call("Matrix.conjTranspose", a), a),
            Mul(a, Call("Matrix.conjTranspose", a)));
        Formula matrices = All("n", Nat(), All("A", Matrix(n),
            Iff(Call("Matrix.PosSemidef", Call("block", f, g, a)), normal)));
        return All("f", RealFunction(), All("g", RealFunction(),
            Imp(product, Imp(high, Imp(low, matrices)))));
    }

    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula RealFunction() => Seq(Real(), To, Real());
    private static Formula Matrix(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Complex());
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(
        Seq(Operatorname, Grp(Seq(name.Split('.').Select((part, index) =>
            index == 0 ? V(part) : Seq(Dot, V(part))).ToArray()))), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
