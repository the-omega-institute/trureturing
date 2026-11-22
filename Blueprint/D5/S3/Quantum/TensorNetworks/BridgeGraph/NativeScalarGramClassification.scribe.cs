using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeScalarGramClassificationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGramClassification";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact dimension criteria for a positive scalar column Gram of a width-three tensor sum.",
        H("Width-three scalar column Gram classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-gram-admissible"),
                DeclarationHandle.Create(Owner + ".ScalarGramAdmissible"),
                H("Admissible dimensions"),
                StatementSource.FromAuthor(Disp(DimensionStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If either input dimension vanishes, the tensor input is empty. Otherwise, " +
                    "the dimensions are admissible when both factors fit into their respective output spaces " +
                    "or when one factor shrinks and the other meets the corresponding threshold. " +
                    "When the input is nonempty and either output dimension vanishes, every clause fails."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-scalar-gram-iff"),
                DeclarationHandle.Create(Owner + ".native_scalar_gram_iff"),
                H("Exact existence criterion"),
                StatementSource.FromAuthor(Disp(GramStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With a shrinking left factor, the three rectangular bounds give the successive " +
                        "requirements on the right output dimension. The Gram has full column rank, so " +
                        "the upper bound on the rank of a width-three tensor sum also gives b ≤ 3a " +
                        "when the right input dimension is positive.")),
                    Paragraph(Text(
                        "For the one-, two- and three-block constructions, split the left inputs into " +
                        "blocks of size at most a. Each block embeds into the same left output coordinates " +
                        "and sends the right inputs to its own block of c output coordinates. The images of " +
                        "the input coordinates are therefore distinct. Scaling the left factors by the " +
                        "square root of lambda gives the prescribed Gram. At the first rectangular threshold, " +
                        "the excess left inputs use the even and odd routes determined by the two parts of " +
                        "the right input.")),
                    Paragraph(Text(
                        "Exchanging the tensor factors permutes the output and input coordinates. " +
                        "The resulting column Gram is the original Gram reindexed by the input permutation, " +
                        "which preserves the scalar identity. This transports the construction and the " +
                        "dimension bounds when the right factor shrinks."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula rows, Formula cols) =>
        Call("Matrix", rows, cols, V("Complex"));
    private static Formula Factors(Formula rows, Formula cols) =>
        new Formula.TypeArrow(Fin(D(3)), Matrix(rows, cols));
    private static Formula Dimensions(Formula body) =>
        All("a", V("Nat"), All("b", V("Nat"), All("c", V("Nat"), All("d", V("Nat"), body))));

    private static Formula Shrinking(Formula a, Formula b, Formula c, Formula d)
    {
        Formula first = And(Le(Mul(D(2), b), Mul(D(3), a)), Le(Mul(D(3), c), Mul(D(2), d)));
        Formula second = And(Lt(Mul(D(3), a), Mul(D(2), b)),
            And(Le(b, Mul(D(2), a)), Le(Mul(D(2), c), d)));
        Formula third = And(Lt(Mul(D(2), a), b), And(Le(b, Mul(D(3), a)), Le(Mul(D(3), c), d)));
        return And(Lt(a, b), Or(first, Or(second, third)));
    }

    private static Formula DimensionStatement()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d");
        Formula regions = Or(And(Le(b, a), Le(c, d)), Or(Shrinking(a, b, c, d), Shrinking(d, c, b, a)));
        return Dimensions(Iff(Call("ScalarGramAdmissible", a, b, c, d),
            Or(Equal(b, D(0)), Or(Equal(c, D(0)), regions))));
    }

    private static Formula GramStatement()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d"), lambda = V("lambda");
        Formula M = V("M"), N = V("N"), r = V("r");
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(r, Colon, Fin(D(3)))), Sp,
            Call("kronecker", Apply(M, r), Apply(N, r)));
        Formula columns = Call("Prod", Fin(b), Fin(c));
        Formula identity = Seq(Open, D(1), Colon, Sp, Matrix(columns, columns), Close);
        Formula gram = Equal(Mul(Call("conjTranspose", sum), sum),
            Call("smul", Call("ofReal", lambda), identity));
        Formula exists = Some("M", Factors(Fin(a), Fin(b)),
            Some("N", Factors(Fin(d), Fin(c)), gram));
        return Dimensions(All("lambda", V("Real"), Logic(Lt(D(0), lambda),
            FormulaLogicOperator.Implies, Iff(exists, Call("ScalarGramAdmissible", a, b, c, d)))));
    }
}
