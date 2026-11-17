using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeScalarGramDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGram";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original width-three factors realize every positive scalar column Gram in the first rectangular dimension region.",
        H("Native scalar-Gram existence in the first region"),
        Blocks(
            Paragraph(Text(
                "For arbitrary natural dimensions a,b,c,d with 2b ≤ 3a and 3c ≤ 2d, and every " +
                "positive real scalar lambda, explicit original three-factor carriers have a tensor " +
                "sum whose column Gram is lambda times the identity. The construction includes odd " +
                "right dimensions, dependent factors, and all zero dimensions.")),
            Describe.Lean(
                DescribeId.Create("native-scalar-gram-exists"),
                DeclarationHandle.Create(Owner + ".native_scalar_gram_exists"),
                H("Original scalar-Gram witness"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The witnesses keep the native factorization F = Σᵣ M(r) ⊗ N(r), with " +
                        "M(r) an a-by-b complex matrix and N(r) a d-by-c complex matrix. The " +
                        "conclusion is FᴴF = lambda • I on Fin b × Fin c, where lambda is coerced " +
                        "from Real to Complex.")),
                    Paragraph(Text(
                        "The left family is the canonical NativeSaturation.leftSlices supplier. " +
                        "For the right family, split the c input columns at c/2. The first residual " +
                        "block routes to right coordinates c+k, and the second routes to " +
                        "c+(k-c/2); their left coordinates are respectively even and odd residual " +
                        "slots. The first j<a branch uses the diagonal route (j,k).")),
                    Paragraph(Text(
                        "The arithmetic hypotheses give 2(b-a) ≤ a and c+(c-c/2) ≤ d. Thus every " +
                        "route is well typed. The three branches are disjoint and recover both input " +
                        "coordinates, so the route is injective. Entrywise expansion identifies the " +
                        "tensor sum with SequentialRegisterCircuit.coordinateMatrix, whose column " +
                        "Gram is the identity. Multiplying the left family by the positive scalar " +
                        "sqrt(lambda) changes that identity Gram to lambda times the identity.")),
                    Paragraph(Text(
                        "No premise a<b, parity premise on c, exact minimal d, factor independence, " +
                        "or universal necessity theorem is used. The statement is a sufficiency result " +
                        "for the two displayed dimension inequalities and does not assert a full " +
                        "all-dimension existence classification."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula SumTerm(Formula index, Formula term) =>
        Seq(new Formula.Subscript(F.Sum, Seq(index, Colon, Call("Fin", D(3)))), Sp, term);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula rows, Formula cols) =>
        Call("Matrix", rows, cols, V("Complex"));
    private static Formula Factors(Formula rows, Formula cols) =>
        new Formula.TypeArrow(Fin(D(3)), Matrix(rows, cols));
    private static Formula Product(Formula left, Formula right) => Call("Prod", left, right);

    private static Formula Statement()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d"), lambda = V("lambda");
        Formula M = V("M"), N = V("N"), r = V("r");
        Formula sum = SumTerm(r, Call("kronecker", Apply(M, r), Apply(N, r)));
        Formula gram = Equal(
            Mul(Call("conjTranspose", sum), sum),
            Call("smul", Call("ofReal", lambda),
                Typed(D(1), Matrix(Product(Fin(b), Fin(c)), Product(Fin(b), Fin(c))))));
        Formula witness = Some("M", Factors(Fin(a), Fin(b)),
            Some("N", Factors(Fin(d), Fin(c)), gram));
        Formula body = All("lambda", V("Real"), Imp(Lt(D(0), lambda), witness));
        return All("a", V("Nat"), All("b", V("Nat"), All("c", V("Nat"),
            All("d", V("Nat"),
                Imp(Le(Mul(D(2), b), Mul(D(3), a)),
                    Imp(Le(Mul(D(3), c), Mul(D(2), d)), body))))));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(Open, value, Colon, Sp, type, Close);
}
