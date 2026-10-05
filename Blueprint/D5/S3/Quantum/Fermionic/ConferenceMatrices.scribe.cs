using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class ConferenceMatricesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/ConferenceMatrices.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive skew conference matrices have order a power of two and flat square.",
        H("Recursive skew conference matrices"),
        Blocks(
            Paragraph(Text("Nat and Int denote natural numbers and integers. Index(0) has two labels; each subsequent label type is the disjoint sum of two copies of the preceding type. SumType is the disjoint sum, and Matrix2x2(a,b,c,d) is the literal two-by-two matrix with first row (a,b) and second row (c,d). Matrix one is the identity matrix, smul is scalar multiplication, transpose is ordinary transpose, and asInt is the natural-to-integer cast. The function letInstance installs its first argument as a local instance in its second argument. inferInstance and inferInstanceAs denote Lean's canonical instance synthesis at the displayed type; the recursive instances use the ordinary sum-type enumeration and decidable equality.")),
            Node("Index", "Recursive labels", new Formula.Aligned([
                Eq(Call("Index", D(0)), Call("Fin", D(2))),
                All("r", N("Nat"), Eq(Call("Index", Add(N("r"), D(1))),
                    Call("SumType", Index(N("r")), Index(N("r")))))]),
                "The displayed equations define the recursive label type.", DescribeRole.Definition),
            Node("indexFintype", "Finite enumeration", new Formula.Aligned([
                Eq(Call("indexFintype", D(0)), Call("inferInstanceAs", Call("Fintype", Call("Fin", D(2))))),
                All("r", N("Nat"), Eq(Call("indexFintype", Add(N("r"), D(1))),
                    Call("letInstance", Call("indexFintype", N("r")),
                        Call("inferInstanceAs", Call("Fintype", Call("SumType", Index(N("r")), Index(N("r"))))))))]),
                "At order zero the enumeration is the finite-two enumeration. Each subsequent enumeration is the finite disjoint-sum enumeration using the preceding enumeration as a local instance.", DescribeRole.Definition),
            Node("indexDecidableEq", "Decidable equality", new Formula.Aligned([
                Eq(Call("indexDecidableEq", D(0)), Call("inferInstanceAs", Call("DecidableEq", Call("Fin", D(2))))),
                All("r", N("Nat"), Eq(Call("indexDecidableEq", Add(N("r"), D(1))),
                    Call("letInstance", Call("indexDecidableEq", N("r")),
                        Call("inferInstanceAs", Call("DecidableEq", Call("SumType", Index(N("r")), Index(N("r"))))))))]),
                "At order zero equality is finite-two equality. At every subsequent order equality is disjoint-sum equality using the preceding equality instance.", DescribeRole.Definition),
            Node("conference", "Matrix recursion", new Formula.Aligned([
                Eq(C(D(0)), Call("Matrix2x2", D(0), D(1), Negate(D(1)), D(0))),
                All("r", N("Nat"), Eq(C(Add(N("r"), D(1))), Call("fromBlocks",
                    C(N("r")), Add(C(N("r")), One(N("r"))),
                    Sub(C(N("r")), One(N("r"))), Negate(C(N("r"))))))]),
                "The four blocks at each doubling are C, C+I, C-I and -C, in that order. All entries are integers.", DescribeRole.Definition),
            Node("conference_properties", "Order, skewness, signs and square", Properties(),
                "The recursive family has order 2^(r+1), zero diagonal and signed off-diagonal entries. Its square is minus the order minus one times the identity. Induction on the doubling step preserves the four-block multiplication identity as well as the signed-entry conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("fgauss-conference-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Add(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Add, rhs);
    private static Formula Sub(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Subtract, rhs);
    private static Formula Negate(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Index(Formula r) => Call("Index", r);
    private static Formula C(Formula r) => Call("conference", r);
    private static Formula One(Formula r) =>
        Parenthesized(Seq(D(1), Colon, Call("Matrix", Index(r), Index(r), N("Int"))));

    private static Formula Properties()
    {
        var r = N("r");
        var i = N("i");
        var j = N("j");
        var cardinality = Call("card", Index(r));
        var entry = Call("val", C(r), i, j);
        return All("r", N("Nat"), Seq(
            Parenthesized(Eq(cardinality, new Formula.Power(D(2), Parenthesized(Add(r, D(1)))))),
            Land, Parenthesized(Eq(Call("transpose", C(r)), Negate(C(r)))),
            Land, Parenthesized(All("i", Index(r), Eq(Call("val", C(r), i, i), D(0)))),
            Land, Parenthesized(All("i", Index(r), All("j", Index(r), new Formula.Logic(
                Parenthesized(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j)),
                FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(
                    Parenthesized(Eq(entry, D(1))), FormulaLogicOperator.Or,
                    Parenthesized(Eq(entry, Negate(D(1)))))))))),
            Land, Parenthesized(Eq(new Formula.Binary(C(r), FormulaBinaryOperator.Multiply, C(r)),
                Call("smul", Negate(Sub(Call("asInt", cardinality), D(1))), One(r))))));
    }
}
