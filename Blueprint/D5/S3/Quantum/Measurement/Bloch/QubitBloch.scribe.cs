using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Bloch;

internal sealed class QubitBlochDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/Bloch/QubitBloch.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic qubit Bloch coordinates and scalar effects.",
        H("Qubit Bloch coordinates"),
        Blocks(
            Node("B", "B", "Real coordinates multiply the three single-qubit Pauli matrices.",
                DescribeRole.Definition, All("a", Vectors(), Equal(Call("B", X("a")),
                    Add(Add(Smul(Typed(Apply(X("a"), D(0)), Complexes()), Apply(X("pauliMatrix"), Qualified("Pauli", "X"))),
                        Smul(Typed(Apply(X("a"), D(1)), Complexes()), Apply(X("pauliMatrix"), Qualified("Pauli", "Y")))),
                        Smul(Typed(Apply(X("a"), D(2)), Complexes()), Apply(X("pauliMatrix"), Qualified("Pauli", "Z"))))))),
            Describe.Lean(DescribeId.Create("qubit-bloch-b-formula"),
                DeclarationHandle.Create(Prefix + "B_formula_core"), H("The Pauli coordinate matrix"),
                StatementSource.FromAuthor(Disp(All("a", Vectors(), Equal(Call("B", X("a")),
                    Mat(Typed(Apply(X("a"), D(2)), Complexes()),
                        Subtract(Typed(Apply(X("a"), D(0)), Complexes()),
                            Multiply(Qualified("Complex", "I"), Typed(Apply(X("a"), D(1)), Complexes()))),
                        Add(Typed(Apply(X("a"), D(0)), Complexes()),
                            Multiply(Qualified("Complex", "I"), Typed(Apply(X("a"), D(1)), Complexes()))),
                        Negate(Typed(Apply(X("a"), D(2)), Complexes()))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The Pauli expansion gives the four complex matrix entries."))),
                DescribeRole.Theorem),
            Node("scalarB", "scalarB", "A real scalar identity is added to the traceless Bloch matrix.",
                DescribeRole.Definition, All("t", Reals(), All("a", Vectors(),
                    Equal(Call("scalarB", X("t"), X("a")),
                        Add(Smul(Typed(X("t"), Complexes()), Identity()), Call("B", X("a")))))))),
        []));

    private static DocumentBlock Node(string id, string title, string prose,
        DescribeRole role, Formula formula) =>
        Describe.Lean(DescribeId.Create("qubit-bloch-" + id.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + id), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Apply(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula X(string name) => F.Id(name);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Vectors() => Call("EuclideanSpace", Reals(), Fin(3));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula Identity() => Typed(D(1), Matrices());
    private static Formula Matrices() => Call("Matrix", Fin(2), Fin(2), Complexes());
    private static Formula Mat(Formula a, Formula b, Formula c, Formula d) => Seq(Begin, Grp(X("pmatrix")), a, Amp, b, RowBreak, c, Amp, d, End, Grp(X("pmatrix")));
}
