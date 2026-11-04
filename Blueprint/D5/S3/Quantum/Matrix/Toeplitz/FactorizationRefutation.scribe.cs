using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Toeplitz;

internal sealed class FactorizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/garciamarco2025toeplitzfactors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No fixed number of ordinary Toeplitz factors suffices after a free invertible left multiplier.",
        H("A field of definition obstruction to uniform Toeplitz factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordinary-toeplitz"),
                DeclarationHandle.Create(Module + ".IsOrdinaryToeplitz"),
                H("Ordinary Toeplitz matrices"),
                StatementSource.FromAuthor(Disp(All("n", Naturals,
                    All("T", Mat(V("n")),
                        IffOf(Call("IsOrdinaryToeplitz", V("T")),
                            OrdinaryBody(V("n"), V("T"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The first index is the row, and Fin n uses indices 0 through n − 1. "
                    + "The definition requires equality between each entry and its adjacent "
                    + "southeast entry whenever both successor indices exist. Fin.val takes a "
                    + "finite index to its natural value; Fin.mk constructs an index from its "
                    + "value and a proof that it is below n. This is equation (1) of the source, "
                    + "with its indices shifted down by one. The predicate also defines the "
                    + "empty-size case, although the factorization assertion only uses positive sizes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-factorization-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The complete uniform factorization assertion"),
                StatementSource.FromAuthor(Disp(IffOf(Call("claim"), FullClaim()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Conjecture 5.1 in Section 5.2 of García-Marco, Márquez-Corbella and "
                        + "Seco, arXiv:2506.16432v1, asserts one positive finite factor count C "
                        + "that works for every positive dimension n and every complex matrix M, "
                        + "including singular matrices. IsUnit P is genuine invertibility of "
                        + "the square complex matrix P. Its position is on the left.")),
                    Paragraph(Text(
                        "The function T is an ordered C-tuple of matrices of exactly the same "
                        + "size as M. List.ofFn T lists them in increasing Fin.val order. "
                        + "List.prod multiplies a list by the recursion prod([]) = 1 and "
                        + "prod(A :: L) = A * prod(L). Thus the displayed product is ordered; "
                        + "no commutativity of matrix multiplication is assumed. The ordinary "
                        + "Toeplitz condition is expanded for every factor. The identity is "
                        + "Toeplitz, so allowing at most C factors gives the same assertion by padding.")),
                    Paragraph(Text(
                        "All matrix products use the usual finite entry sum, with complex "
                        + "multiplication and addition:"), Math(In(MatrixMultiplication())))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-factorization-refutation"),
                DeclarationHandle.Create(Module + ".result"),
                H("The uniform factorization assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(FullClaim())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix an arbitrary positive C. Set r = 4C and n = 2r = 8C, choose "
                        + "r squared complex entries algebraically independent over the rationals, "
                        + "and arrange them as a matrix X. Such finite independent families exist "
                        + "because a transcendence basis of the uncountable field of complex "
                        + "numbers over the countable rational field cannot be finite. Let "
                        + "M be the block matrix with top blocks I and X and bottom blocks zero. "
                        + "These choices precede any proposed factors.")),
                    Paragraph(Text(
                        "Suppose M = P N, where P is invertible and N is the ordered product "
                        + "of C ordinary Toeplitz factors. Adjacent-diagonal equality gives a "
                        + "coefficient function of the integer row-minus-column offset, using "
                        + "LiCurvatureCriterion.toeplitzMatrix. Only 2n − 1 offsets occur. "
                        + "Let K be the single intermediate field of the complex numbers "
                        + "generated over the rationals by all C(2n − 1) coefficients. Every "
                        + "entry of every factor and of N lies in K, since matrix multiplication "
                        + "uses finite sums and products. N itself need not be Toeplitz.")),
                    Paragraph(Text(
                        "From N = P inverse times M, every actual row of N lies in the graph "
                        + "of u ↦ uX. From M = PN, the first-r-coordinate projections of the "
                        + "actual rows of N span the full complex r-dimensional row space. "
                        + "LinearRado.exists_nonsingular_rows selects r actual rows whose "
                        + "first blocks form a nonsingular square matrix A. Their second "
                        + "blocks form B, and graph membership gives B = AX. Both A and B "
                        + "have entries in K; no arbitrary complex row combinations are used "
                        + "as K-valued coordinates.")),
                    Paragraph(Text(
                        "The inclusion K into the complex numbers preserves determinants. "
                        + "The nonzero complex determinant therefore gives a nonzero determinant "
                        + "over K. Inverting A over K yields X = A inverse times B after "
                        + "inclusion. All r squared independent entries of X consequently lie "
                        + "in K, and their independence transfers along the injective rational "
                        + "algebra map. Hence r squared is at most the transcendence degree "
                        + "of K over the rationals.")),
                    Paragraph(Text(
                        "For the internal copies of the generating coefficients, their "
                        + "intermediate-field adjoin is all of K. That field adjoin is "
                        + "algebraic over their algebra adjoin, and algebraicity transports "
                        + "to K. Thus its transcendence degree is at most C(2n − 1). "
                        + "But C(2n − 1) + C = r squared, contradicting C > 0. This excludes "
                        + "every proposed positive uniform C. The argument uses no coefficient "
                        + "of P in the parameter count.")),
                    Paragraph(Text(
                        "The separately printed numerical consequence concerning Toep_n and "
                        + "Toep_n^Inv remains unresolved here. Failure of this factorization "
                        + "assertion does not establish an unbounded difference of those "
                        + "two global Toeplitz numbers. Conjectures 5.2 and 5.3 are separate statements."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("garcia-marco-2025-uniform-toeplitz-factorization"),
                    ResolutionKind.Refuted)))));

    private static Formula FullClaim()
    {
        Formula c = V("C"), n = V("n"), m = V("M"), p = V("P"), t = V("T");
        Formula factors = All("k", Fin(c), OrdinaryBody(n, Apply(t, V("k"))));
        Formula orderedProduct = QualifiedCall("List", "prod", QualifiedCall("List", "ofFn", t));
        return Some("C", Naturals, And(Less(D(0), c),
            All("n", Naturals, Imp(Less(D(0), n), All("M", Mat(n),
                Some("P", Mat(n), Some("T", Arrow(Fin(c), Mat(n)),
                    And(Call("IsUnit", p), And(factors,
                        Eqn(m, Multiply(p, orderedProduct)))))))))));
    }

    private static Formula OrdinaryBody(Formula n, Formula matrix)
    {
        Formula i = V("i"), j = V("j"), hi = V("hi"), hj = V("hj");
        Formula nextI = Add(QualifiedCall("Fin", "val", i), D(1));
        Formula nextJ = Add(QualifiedCall("Fin", "val", j), D(1));
        return All("i", Fin(n), All("j", Fin(n),
            All("hi", Less(nextI, n), All("hj", Less(nextJ, n),
                Eqn(Apply(matrix, i, j),
                    Apply(matrix, QualifiedCall("Fin", "mk", nextI, hi), QualifiedCall("Fin", "mk", nextJ, hj)))))));
    }

    private static Formula MatrixMultiplication()
    {
        Formula n = V("n"), a = V("A"), b = V("B"), i = V("i"), j = V("j"), k = V("k");
        Formula sum = Seq(new Formula.Subscript(Sum, Typed(k, Fin(n))), Sp,
            Multiply(Apply(a, i, k), Apply(b, k, j)));
        return All("n", Naturals, All("A", Mat(n), All("B", Mat(n),
            All("i", Fin(n), All("j", Fin(n), Eqn(Apply(Multiply(a, b), i, j), sum))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), Complexes);
    private static Formula Call(string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(V(name))), args);
    private static Formula QualifiedCall(string space, string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(V(space), Dot, V(name))), args);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
