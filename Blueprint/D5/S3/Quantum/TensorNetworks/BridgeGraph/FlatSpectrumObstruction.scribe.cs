using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class FlatSpectrumObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar Gram imposes a dimension obstruction on native width-three bridge matrices.",
        H("Flat spectra and the width-three bridge"), Blocks(
            Paragraph(Text("All dimensions are natural numbers and all local matrices are unrestricted complex rectangular matrices. The native map F is QuantumMaxFlowBound.flow M N, the sum over r in Fin 3 of M r tensor N r. Its rows are Fin a times Fin d and its columns are Fin b times Fin c. The notation conjTranspose means the complex conjugate transpose, ofReal is the real-to-complex embedding, and smul is scalar multiplication of a matrix. Each displayed identity has its indicated matrix index type.")),
            Item("claim", "The universal ordered-cone assertion", ClaimFormula(),
                "The six domain premises are positivity and ordering for each pair and the two quadratic cone inequalities. The same positive real scalar occurs in both implications. When ad equals bc, both implications apply, so both Gram identities are required.", DescribeRole.Definition),
            Item("obstruction", "The structural dimension obstruction", ObstructionFormula(),
                "A scalar column Gram and the strict inequality 5a < 2b force 3c <= d. The theorem only needs c positive; it therefore includes the positive dimension case. The proof first makes the common kernel of the three M maps trivial. For each r, the kernel of the other two maps has dimension at least b-2a, and its image under M r has the same dimension. Two such images cannot be orthogonal because their dimensions sum to more than a. Testing a relation between the nine products M r adjoint times M s on vectors in these kernels isolates each coefficient and proves linear independence. The native Gram equation then forces every N r adjoint times N s to be a scalar identity. Taking the scalar from any fixed diagonal coordinate gives a matrix H. The stacked M map satisfies J adjoint (H tensor I a) J = ofReal lam times I b, so b <= a rank H and rank H = 3. The concatenated N map has Gram H tensor I c, of rank 3c, and consequently d >= 3c. The block-rank formula is applied from ConstructionReduction.Blocks.rank_block.", DescribeRole.Theorem),
            Item("result", "Failure at the equality boundary", new Formula.Not(Op("claim")),
                "Substitute a=c=5 and b=d=13. The cone expressions are 194 <= 195 on both sides, and ad=bc=65. The required column Gram would force 15 <= 13, since 26 > 25. Thus the universal flat-spectrum assertion is false. This concerns equal nonzero singular values in the finite native family; it does not dispute rank attainment, change the tensor grouping, assert a physical realization, or establish a continuum or RT claim.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Item(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bridge-flat-" + name), DeclarationHandle.Create(Owner + "." + name),
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
            Imp(Cone("a", "b"), Imp(Cone("c", "d"), exists))))));
        return Seq(Op("claim"), Sp, Iff, Sp, P(OverDimensions(premises)));
    }

    private static Formula ObstructionFormula()
    {
        Formula body = Imp(ColumnGram(), LeF(Mul(D(3), X("c")), X("d")));
        body = All("lam", RealF(), Imp(LtF(D(0), X("lam")), body));
        body = Imp(LtF(D(0), X("c")), Imp(LtF(Mul(D(5), X("a")), Mul(D(2), X("b"))), body));
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
