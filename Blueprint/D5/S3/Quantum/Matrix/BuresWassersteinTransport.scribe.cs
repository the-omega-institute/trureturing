using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class BuresWassersteinTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive transport certificate identifies the actual unique Wasserstein barycenter.",
        H("Finite Bures–Wasserstein transport certificates"),
        Blocks(Describe.Lean(DescribeId.Create("finite-barycenter-of-dual"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/BuresWassersteinTransport.finite_barycenter_of_dual"),
            H("Global minimum, uniqueness and actual selection"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/bhatiajainlim2018wasserstein")),
            Blocks(Paragraph(Text(
                "Here m and n are arbitrary natural numbers, matrices are complex m×m matrices, "
                + "and J(X)=Σⱼwⱼ d_W(X,Aⱼ)² uses HwangKimNearOrderRefutation.buresWassersteinDistance. "
                + "Every input, W and every transport is positive definite, every weight is strictly "
                + "positive, the weights sum to one, TⱼWTⱼ=Aⱼ and ΣⱼwⱼTⱼ=I. The result proves the "
                + "global lower bound for every positive definite X, characterizes J(X)≤J(W) by X=W, "
                + "and proves that the existing Classical.epsilon definition wassersteinBarycenter w A "
                + "selects W. In particular equality of objective values characterizes W, and any "
                + "other global minimizer equals W. Existence is supplied by the given certificate; "
                + "this theorem does not construct transports for arbitrary inputs.")),
                Paragraph(Text(
                "The proof directly reuses the original private fidelity_young_rigid, fidelity_transport "
                + "and bures_sq proofs. Its finite weighted gap identity gives a nonnegative objective "
                + "difference. Equality forces every gap to vanish; positivity of the weights and "
                + "normalization ensure there is an input, and one invertible transport gives X=W. "
                + "The epsilon predicate is the actual global argmin predicate over positive definite "
                + "matrices, not a transport-defined substitute for the mean. A checked exact application for arbitrary finite strictly positive diagonal data identifies the actual barycenter as diag((Σⱼwⱼ√aⱼₖ)²) and the actual logarithmic mean as diag(exp(Σⱼwⱼlog aⱼₖ)). Reusing scalar weighted AM–GM and its equality theorem also proves their Loewner comparison and equality iff all input coordinates coincide. This is transient application evidence, not a separately retained bind-only API; the full arbitrary commuting family and near-order theorem remain open.")),
                Paragraph(Text(
                "The established mathematical characterization is due to Bhatia–Jain–Lim, "
                + "On the Bures–Wasserstein Distance Between Positive Definite Matrices, "
                + "arXiv:1712.01504v1, Theorem 8 and equations (62)–(63), together with the "
                + "positive Riccati characterization (9). The elementary dual proof also appears "
                + "as Lemma 2 of the Ma–Zhang revision2 note, retained at issue #29594 (CC BY 4.0). "
                + "Haobo Ma: ChronoAI, Singapore. Wenlin Zhang: NUS and ChronoAI, Singapore. "
                + "The finite formal interface is a research-to-formal return, not a new scientific "
                + "optimality characterization. It does not establish the note's other seven groups. "
                + "The binary equal-weight original refutation remains reusable and unchanged in scope."))),
            DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, b);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Iff, P(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula FinN => C("Fin", V("n"));
    private static Formula Mat => C("Matrix", C("Fin", V("m")), C("Fin", V("m")), Seq(Mathbb, Grp(V("C"))));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula Sum(Formula x) => Seq(new Formula.Subscript(F.Sum, Seq(V("j"), Colon, Sp, FinN)), Sp, P(x));
    private static Formula J(Formula x) => Sum(Mul(C("w", V("j")),
        new Formula.Power(C("buresWassersteinDistance", x, C("A", V("j"))), D(2))));

    private static Formula Statement()
    {
        Formula wj = C("w", V("j")), aj = C("A", V("j")), tj = C("T", V("j"));
        Formula assumptions = And(All("j", FinN, Lt(D(0), wj)),
            And(Eq(Sum(wj), D(1)), And(All("j", FinN, C("PosDef", aj)),
            And(C("PosDef", V("W")), And(All("j", FinN, C("PosDef", tj)),
            And(All("j", FinN, Eq(Mul(Mul(tj, V("W")), tj), aj)),
                Eq(Sum(Seq(wj, Sp, Cdot, Sp, tj)), D(1))))))));
        Formula conclusion = And(All("X", Mat, Imp(C("PosDef", V("X")), Le(J(V("W")), J(V("X"))))),
            And(All("X", Mat, Imp(C("PosDef", V("X")), Iff(Le(J(V("X")), J(V("W"))), Eq(V("X"), V("W"))))),
                Eq(C("wassersteinBarycenter", V("w"), V("A")), V("W"))));
        return Disp(All("m", Nat, All("n", Nat, All("w", Arrow(FinN, Real),
            All("A", Arrow(FinN, Mat), All("T", Arrow(FinN, Mat), All("W", Mat,
                Imp(assumptions, conclusion))))))));
    }
}
