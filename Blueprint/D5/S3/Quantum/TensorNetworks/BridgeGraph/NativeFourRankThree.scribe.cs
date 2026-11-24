using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeFourRankThreeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourRankThree";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right dimension bounds from a rank-three Hermitian coefficient.",
        H("Rank-three coefficient kernels at width four"),
        Blocks(
            Describe.Lean(DescribeId.Create("rank-three-small-defect-four-bound"),
                DeclarationHandle.Create(Owner + ".rank_three_small_defect_four_bound"),
                H("Dimension bounds from a rank-three compression kernel member"),
                StatementSource.FromAuthor(Disp(RankThreeBound())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A rank-three Hermitian coefficient yields an isometric right combination and " +
                        "an orthogonal combination of rank at most the difference of the right dimensions. " +
                        "On the kernel of the latter, the tensor has width at most three.")),
                    Paragraph(Text(
                        "When the right dimensions violate the stronger bound, the isolated isometry " +
                        "on that kernel determines the right output slice. The small row defect forces the " +
                        "paired left factor to be a coisometry. Projecting to the perpendicular right " +
                        "output then bounds its rank by the three remaining factors and the row defect.")),
                    Paragraph(Text(
                        "At (4,5,4,5), (5,6,4,5), and (5,6,5,6), the row defects are zero, one, and zero. " +
                        "They are smaller than the corresponding thresholds three, three, and four. " +
                        "At each size the stronger dimension inequality forbids a rank-three coefficient."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Apply(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Bind(FormulaQuantifier q, string name, Formula type, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), type, body);
    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);
    private static Formula Parens(Formula formula) => Seq(Open, formula, Close);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parens(a), op, Parens(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Matrix(Formula rows, Formula cols) => Call("Matrix", rows, cols, V("Complex"));
    private static Formula Factors(Formula rows, Formula cols) =>
        new Formula.TypeArrow(Fin(D(4)), Matrix(Fin(rows), Fin(cols)));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Ct(Formula matrix) => Call("conjTranspose", matrix);


    private static Formula RankThreeBound()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d"), lam = V("lambda");
        Formula X = V("X"), Y = V("Y"), i = V("i"), T = V("T");
        Formula tensor = Seq(new Formula.Subscript(F.Sum, Seq(i, Colon, Fin(D(4)))), Sp,
            Call("kronecker", Apply(X, i), Apply(Y, i)));
        Formula cols = Call("Prod", Fin(b), Fin(c));
        Formula identity = Parens(Seq(D(1), Colon, Sp, Matrix(cols, cols)));
        Formula gram = Eq(Mul(Ct(tensor), tensor), Call("smul", Call("ofReal", lam), identity));
        Formula square = Matrix(Fin(D(4)), Fin(D(4)));
        Formula kernel = Some("T", square, And(Call("IsHermitian", T),
            And(Eq(Call("compression", X, T), D(0)), Eq(Call("rank", T), D(3)))));
        Formula smallDefect = Lt(Sub(Mul(a, d), Mul(b, c)), Sub(Mul(D(2), c), d));
        Formula conclusion = And(Le(Mul(D(6), c), Mul(D(5), d)),
            Implies(smallDefect, Le(Mul(D(4), c), Mul(D(3), d))));
        Formula law = All("lambda", V("Real"), Implies(Lt(D(0), lam),
            Implies(Lt(a, b), Implies(gram, Implies(kernel, conclusion)))));
        return All("a", V("Nat"), All("b", V("Nat"), All("c", V("Nat"), All("d", V("Nat"),
            All("X", Factors(a, b), All("Y", Factors(d, c), law))))));
    }
}
