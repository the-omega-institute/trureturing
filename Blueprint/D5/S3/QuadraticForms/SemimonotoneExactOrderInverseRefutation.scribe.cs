using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SemimonotoneExactOrderInverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Name(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula App(string s, params Formula[] args) => new Formula.Apply(Name(s), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp,
        Par(Seq(V(s), Colon, Sp, t)), Comma, Sp, Par(b));
    private static Formula All(Formula s, Formula t, Formula b) => Seq(Forall, Sp,
        Par(Seq(s, Colon, Sp, t)), Comma, Sp, Par(b));
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists, Sp,
        Par(Seq(V(s), Colon, Sp, t)), Comma, Sp, Par(b));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula IffEq(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula NN => Seq(Mathbb, Grp(V("N")));
    private static Formula RR => Seq(Mathbb, Grp(V("R")));
    private static Formula N => V("n");
    private static Formula K => V("k");
    private static Formula A => V("A");
    private static Formula Index => App("Fin", N);
    private static Formula MatrixType => App("Matrix", Index, Index, RR);
    private static Formula Nk => new Formula.Binary(N, FormulaBinaryOperator.Subtract, K);
    private static Formula Card => App("card", Alpha);
    private static Formula Block => new Formula.Subscript(A, Seq(Alpha, Alpha));
    private static Formula Body => All("n", NN, All("k", NN, All("A", MatrixType,
        Imp(Leq(D(3), N), Imp(Leq(D(1), K), Imp(Lt(K, N),
            Imp(App("IsExactOrder", N, K, A), And(Lt(App("det", A), D(0)),
                And(App("IsUnit", A), App("IsZMatrix", new Formula.Superscript(A, Seq(Minus, D(1)))))))))))));
    private static DocumentBlock.Describe Definition(string name, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        var iota = Iota;
        var x = V("x");
        var xi = App("x", V("i"));
        var semi = All("x", new Formula.TypeArrow(iota, RR),
            Imp(Ne(x, D(0)), Imp(All("i", iota, Leq(D(0), xi)),
                Some("i", iota, And(Lt(D(0), xi), Leq(D(0),
                    new Formula.Subscript(App("mulVec", A, x), V("i"))))))));
        var exact = And(Leq(K, N), And(
            All(Alpha, App("Finset", Index), Imp(Eqn(Card, Nk), App("Semimonotone", Block))),
            All(Alpha, App("Finset", Index), Imp(Lt(Nk, Card), new Formula.Not(App("Semimonotone", Block))))));
        var z = All("i", iota, All("j", iota,
            Imp(Ne(V("i"), V("j")), Leq(new Formula.Subscript(A, Seq(V("i"), V("j"))), D(0)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A four-dimensional singular matrix has exact semimonotone order three, so exact semimonotone order does not force a negative determinant or an inverse.",
            H("Exact semimonotone order does not imply invertibility"), Blocks(
                Paragraph(Text("Source: Bharat Pratap Chauhan and Dipti Dubey, On semimonotone matrices of exact order two, arXiv:2603.00639v1, Section 2, Definition 3.1 and Remark 4.1, second unlettered bullet. The binding version is available at https://arxiv.org/html/2603.00639v1. The question reads: “Is it true that if A belongs to E_{0_k}, then det A < 0 and A inverse exists and is a Z-matrix?” Its introductory range is n at least three and one at most k less than n. The first bullet concerning negative-entry counts is a separate question.")),
                Definition("Semimonotone", IffEq(App("Semimonotone", A), semi),
                    "For an arbitrary finite index type iota and a real square matrix A, every nonzero entrywise nonnegative real vector must have a strictly positive coordinate whose image coordinate is nonnegative. Zero coordinates are allowed. This is the ordinary E_0 predicate from Section 2, rather than strict semimonotonicity or the source's almost-class condition."),
                Definition("IsExactOrder", IffEq(App("IsExactOrder", N, K, A), exact),
                    "Here alpha ranges over every finite subset of Fin n, card denotes its cardinality, and A with subscripts alpha alpha is the actual principal submatrix, indexed by the subtype alpha. Every block of size n-k is semimonotone, and every block of every larger size fails semimonotonicity. Sizes are automatically at most n. The condition k at most n is explicit. Fin n relabels the source's indices one through n by zero through n-1."),
                Definition("IsZMatrix", IffEq(App("IsZMatrix", A), z),
                    "For every pair of distinct indices the corresponding entry is nonpositive, exactly the Z-matrix definition in Section 2. Diagonal entries are unrestricted."),
                Definition("claim", IffEq(V("claim"), Body),
                    "The assertion quantifies over every natural n and k and every real n by n matrix. Its hypotheses are n at least three, one at most k, k less than n and membership in E_{0_k}. Its conclusion contains all three source requirements: negative determinant, actual invertibility, and a Z-matrix inverse. IsUnit A means that A is a unit in the matrix ring, equivalently it has a two-sided matrix inverse. Although Mathlib's inverse operation is total, IsUnit A is a separate conjunct, so the assertion does not interpret a singular matrix's total inverse as an existing inverse. There is no symmetry, Z-matrix or nonsingularity hypothesis on A."),
                Definition("counterexample", Eqn(V("counterexample"),
                    App("ofRows", App("row", D(1), Seq(Minus, D(5)), Seq(Minus, D(2)), Seq(Minus, D(2))),
                        App("row", Seq(Minus, D(5)), D(1), Seq(Minus, D(2)), Seq(Minus, D(2))),
                        App("row", Seq(Minus, D(2)), Seq(Minus, D(2)), D(1), Seq(Minus, D(5))),
                        App("row", Seq(Minus, D(2)), Seq(Minus, D(2)), Seq(Minus, D(5)), D(1)))),
                    "The displayed four rows specify the real matrix A. Its diagonal is one; each off-diagonal entry is at most minus two. Each singleton principal block is [1] and is semimonotone. In every larger principal block and every row choose one other index: the diagonal and that off-diagonal entry sum to at most minus one, and all remaining entries are nonpositive. Thus the all-ones vector is nonzero and nonnegative, and every image coordinate is strictly negative. Every such block fails semimonotonicity. Consequently A belongs to E_{0_3}, with n=4 and k=3."),
                Definition("kernelVector", Eqn(V("kernelVector"), App("vector", D(1), D(1), Seq(Minus, D(1)), Seq(Minus, D(1)))),
                    "The real column vector (1,1,-1,-1) is nonzero and its product with A is zero. The equal-sized sign blocks cancel exactly: each row gives either 1-5+2+2 or -2-2-1+5. This proves singularity by ordinary matrix algebra, independently of testing finitely many numerical matrices."),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("The full second-bullet assertion is false"), StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "Specialize the universal assertion to n=4, k=3 and the displayed matrix. Exact-order membership was established for every principal index subset. A negative determinant would be nonzero, and Mathlib's kernel theorem would then force the displayed nonzero kernel vector to vanish, a contradiction. The same kernel vector also rules out an actual inverse; no property of the total inverse on singular matrices is used. The failure occurs in the allowed n-k=1 boundary case, through cancellation between two groups of coordinates with opposite signs. This refutes the universal conjunction, without asserting that every individual inverse-Z conclusion fails or settling the distinct exact-order-two conjecture."))), DescribeRole.Theorem))));
    }
}
