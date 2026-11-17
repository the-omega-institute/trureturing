using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class RestrictedFlatSpectrumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient-direction rigidity refutes the restricted native scalar-Gram cone.",
        H("The restricted flat-spectrum cone"), Blocks(
            Paragraph(Text("All dimensions are natural numbers and all local matrices are unrestricted complex rectangular matrices. The native map F is QuantumMaxFlowBound.flow M N, the sum over r in Fin 3 of M r tensor N r. Its rows are Fin a times Fin d and its columns are Fin b times Fin c. The notation conjTranspose means the complex conjugate transpose, ofReal is the real-to-complex embedding, and smul is scalar multiplication of a matrix. Each displayed identity has its indicated matrix index type.")),
            Item("claim", "The universal eight-premise assertion", ClaimFormula(),
                "The eight premises are positivity and ordering for each pair, the two quadratic cone inequalities, 2b <= 5a and 2d <= 5c. The same positive real scalar occurs in both implications. When ad equals bc, both implications apply, so both Gram identities are required.", DescribeRole.Definition),
            Item("obstruction", "The structural dimension obstruction", ObstructionFormula(),
                "A scalar column Gram with c positive and b > 2a forces 3c <= d; no positivity assumption on a is needed. The common kernel of the M maps is trivial. Their stack has b-dimensional range in the 3a-dimensional ambient space. For each nonzero z in C^3, the a-dimensional subspace of vectors (z r times u) intersects this range nontrivially, since b+a > 3a. Thus there are x and nonzero u with M r x = z r times u for every r. Applying a proposed relation between the nine adjoint products to x on both sides gives the quadratic form of its coefficient matrix times the nonzero inner product of u with itself. This vanishes for every z, so complex polarization forces the coefficient matrix to vanish. The original scalar_cross_grams lemma then makes every N r adjoint times N s a scalar identity. The original stack_gram, concat_gram and rank_kronecker_one lemmas give b <= a rank H, rank H = 3, and 3c <= d.", DescribeRole.Theorem),
            Item("result", "Failure at the equality boundary", new Formula.Not(Op("claim")),
                "Substitute a=c=2 and b=d=5. Both quadratic inequalities are 29 <= 30, both ratio premises are 10 <= 10, and ad=bc=10. All eight premises hold. Equality requires both Gram identities for the same M, N and positive scalar. The column identity alone would force 6 <= 5 because 5 > 4, which is impossible. The old strict hypothesis 5a < 2b fails here: both sides equal 10. This is a result about arbitrary finite complex rectangular matrices in the native width-three grouping. It does not dispute rank attainment and carries no physical realization, continuum, RT, optimal-threshold or literature-originality claim.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Item(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bridge-restricted-flat-" + name), DeclarationHandle.Create(Owner + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula ClaimFormula()
    {
        Formula bodies = And(LtF(D(0), X("lam")), And(
            Imp(LeF(Mul(X("b"), X("c")), Mul(X("a"), X("d"))), ColumnGram()),
            Imp(LeF(Mul(X("a"), X("d")), Mul(X("b"), X("c"))), RowGram())));
        Formula exists = Ex("M", Matrices("a", "b"), Ex("N", Matrices("d", "c"), Ex("lam", RealF(), bodies)));
        Formula premises = Imp(LtF(D(0), X("a")), Imp(LeF(X("a"), X("b")),
            Imp(LtF(D(0), X("c")), Imp(LeF(X("c"), X("d")),
            Imp(Cone("a", "b"), Imp(Cone("c", "d"),
            Imp(LeF(Mul(D(2), X("b")), Mul(D(5), X("a"))),
            Imp(LeF(Mul(D(2), X("d")), Mul(D(5), X("c"))), exists))))))));
        return Seq(Op("claim"), Sp, Iff, Sp, P(OverDimensions(premises)));
    }

    private static Formula ObstructionFormula()
    {
        Formula body = Imp(ColumnGram(), LeF(Mul(D(3), X("c")), X("d")));
        body = All("lam", RealF(), Imp(LtF(D(0), X("lam")), body));
        body = Imp(LtF(D(0), X("c")), Imp(LtF(Mul(D(2), X("a")), X("b")), body));
        return OverDimensions(All("M", Matrices("a", "b"), All("N", Matrices("d", "c"), body)));
    }

    private static Formula Flow() => At(Qualified("QuantumMaxFlowBound", "flow"), X("M"), X("N"));
    private static Formula Adj(Formula x) => At(Op("conjTranspose"), x);
    private static Formula ColumnGram() => Equal(Mul(Adj(Flow()), Flow()), ScalarIdentity(Product(Fin("b"), Fin("c"))));
    private static Formula RowGram() => Equal(Mul(Flow(), Adj(Flow())), ScalarIdentity(Product(Fin("a"), Fin("d"))));
    private static Formula ScalarIdentity(Formula index) => At(Op("smul"), At(Op("ofReal"), X("lam")),
        Typed(D(1), MatrixF(index, index)));
    private static Formula Cone(string a, string b) => LeF(Add(Mul(X(a), X(a)), Mul(X(b), X(b))), Mul(Mul(D(3), X(a)), X(b)));
    private static Formula Matrices(string a, string b) => new Formula.TypeArrow(At(Op("Fin"), D(3)), MatrixF(Fin(a), Fin(b)));
    private static Formula MatrixF(Formula a, Formula b) => At(Op("Matrix"), a, b, Seq(Mathbb, Grp(X("C"))));
    private static Formula Fin(string n) => At(Op("Fin"), X(n));
    private static Formula Product(Formula a, Formula b) => P(Seq(a, Sp, Times, Sp, b));
    private static Formula RealF() => Seq(Mathbb, Grp(X("R")));
    private static Formula NatF() => Seq(Mathbb, Grp(X("N")));
    private static Formula X(string s) => F.Id(s);
    private static Formula Op(string s) => Seq(Operatorname, Grp(X(s)));
    private static Formula Qualified(string a, string b) => Seq(Op(a), Dot, Op(b));
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula t) => P(Seq(f, Sp, Colon, Sp, t));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Sp, Typed(X(n), t), Comma, Sp, P(f));
    private static Formula Ex(string n, Formula t, Formula f) => Seq(Exists, Sp, Typed(X(n), t), Comma, Sp, P(f));
    private static Formula OverDimensions(Formula f) => All("a", NatF(), All("b", NatF(), All("c", NatF(), All("d", NatF(), f))));
    private static Formula Mul(Formula a, Formula b) => P(Seq(a, Sp, Cdot, Sp, b));
    private static Formula Add(Formula a, Formula b) => P(Seq(a, Sp, Plus, Sp, b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
}
