using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class FactorialConvolutionFirstColumnDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/kurkov2024a370380");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A factorial convolution invariant identifies the first column of A370380.",
        H("The First-Column Bridge for OEIS A370380"),
        Blocks(
            Paragraph(Text("All indices and values are natural numbers. The notation range(t) "
                + "means the natural numbers strictly below t. The function a is abstract: "
                + "its interpretation as connected-permutation cardinalities is assumed "
                + "through a(1)=1 and Bowen's factorial convolution, not proved here.")),
            Node("array", "The recursively defined array", ArrayFormula(),
                "The zeroth row is constant one. Each later entry is the shifted previous "
                + "entry multiplied by k+2, plus the previous row's prefix through k.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("factorial_convolution_invariant", "The two-variable convolution invariant",
                InvariantFormula(),
                "Induction on n separates the final factorial term. Linearity turns the "
                + "remaining row recurrence into a shifted convolution and a prefix of "
                + "convolutions. Adjacent ascending factorials telescope that prefix.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("factorial_convolution_first_column", "The first column is determined by Bowen data",
                BridgeFormula(),
                "At k=0 the invariant equals (n+1)(n+1)!. Bowen's convolution at n+2, "
                + "after separating its last term and using a(1)=1, has the same value. "
                + "Strong induction cancels all terms with positive factorial index and "
                + "identifies the remaining zeroth terms.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("a370380-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ArrayFormula() => Disp(new Formula.Aligned([
        Seq(F.Id("A"), Colon, Sp, Naturals(), Sp, To, Sp, Naturals(), Sp, To, Sp, Naturals()),
        Seq(Bound("k"), Sp, Equal(A(D(0), K()), D(1))),
        Seq(Bound("n", "k"), Sp,
            Equal(A(Add(N(), D(1)), K()),
                Add(Mul(Add(K(), D(2)), A(N(), Add(K(), D(1)))),
                    SumOver("j", Add(K(), D(1)), A(N(), J())))))
    ]));

    private static Formula InvariantFormula() => Disp(Seq(Bound("n", "k"), Sp,
        Equal(SumOver("r", Add(N(), D(1)),
                Mul(Factorial(R()), A(Subtract(N(), R()), K()))),
            Mul(Add(N(), D(1)), Call("ascFactorial", Add(K(), D(2)), N())))));

    private static Formula BridgeFormula()
    {
        Formula bowen = Seq(
            Bound("m"), Sp,
            Implication(
                Seq(D(1), Sp, Le, Sp, M()),
                Equal(
                    Factorial(M()),
                    SumOver("r", M(),
                        Mul(Factorial(R()), Call("a", Subtract(M(), R())))))));
        Formula assumptions = Seq(Equal(Call("a", D(1)), D(1)), Sp, Land, Sp, bowen);
        Formula conclusion = Seq(Bound("n"), Sp,
            Equal(A(N(), D(0)), Call("a", Add(N(), D(2)))));
        return Disp(Seq(BoundFunction("a"), Sp,
            Implication(Parenthesized(assumptions), conclusion)));
    }

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula J() => F.Id("j");
    private static Formula R() => F.Id("r");
    private static Formula M() => F.Id("m");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula BoundFunction(string name) => Seq(
        Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Sp, To, Sp, Naturals(), Comma);
    private static Formula Bound(params string[] names)
    {
        List<Formula> variables = [];
        foreach (var name in names)
        {
            if (variables.Count > 0) variables.AddRange([Comma, Sp]);
            variables.Add(F.Id(name));
        }
        return Seq(Forall, Sp, Seq([.. variables]), Colon, Sp, Naturals(), Comma);
    }
    private static Formula A(Formula row, Formula column) =>
        new Formula.Apply(F.Id("A"), [row, column]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula SumOver(string variable, Formula bound, Formula body) => Seq(
        new Formula.Subscript(F.Sum,
            Seq(F.Id(variable), Sp, InMacro, Sp, Call("range", bound))), Sp, Parenthesized(body));
    private static Formula Factorial(Formula value) => Seq(Parenthesized(value), Bang);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Implication(Formula left, Formula right) =>
        Seq(left, Sp, Implies, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
