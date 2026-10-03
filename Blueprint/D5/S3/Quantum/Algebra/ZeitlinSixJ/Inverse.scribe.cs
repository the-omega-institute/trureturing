using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class InverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J Inverse"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("inverse_moment_open", "inverse moment open", F0(),
                "Identity (2.10) holds for all distinct positive j and l below N. The diagonal Green entry at the central spin is the reciprocal N times the Casimir difference.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("indexParity", "indexParity", F1(),
                "The displayed equation is the defining expression of indexParity.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("symmetric_jacobi_intertwiner_unique", "symmetric jacobi intertwiner unique", F2(),
                "A connected Jacobi matrix determines each eigen-column from its last coordinate by reverse induction. Symmetry and the last diagonal entry therefore determine the whole intertwiner.", DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("physicalC0", "physicalC0", F3(),
                "The displayed equation is the defining expression of physicalC0.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalX", "physicalX", F4(),
                "The displayed equation is the defining expression of physicalX.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalM", "physicalM", F5(),
                "The displayed equation is the defining expression of physicalM.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalV", "physicalV", F6(),
                "The displayed equation is the defining expression of physicalV.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalTprime", "physicalTprime", F7(),
                "The displayed equation is the defining expression of physicalTprime.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalZ", "physicalZ", F8(),
                "The displayed equation is the defining expression of physicalZ.", DescribeRole.Definition, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-inverse-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, N("N"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(D(1),
        FormulaRelationOperator.LessThanOrEqual, N("j"))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.LessThan, N("N"))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(D(1),
        FormulaRelationOperator.LessThanOrEqual, N("l"))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Relation(N("l"), FormulaRelationOperator.LessThan, N("N"))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.NotEqual,
        N("l"))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Seq(Sum, Underscore,
        Grp(Seq(N("i"), InMacro, Call("range", new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))), Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real",
        Call("asNat", new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), Call("casimir", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("W", N("N"), new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), N("j"), N("l"))), D(2)))))), FormulaRelationOperator.Equal,
        Call("div", D(1), new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asReal",
        Call("real", N("N")))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Absolute(new
        Formula.Binary(Parenthesized(Call("asReal", Call("real", N("j")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("real", N("l")))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("real", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(Call("real", N("l"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))))))))))))))));

    private static Formula F1() =>
        Disp(All("m", N("Nat"), All("b", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("indexParity", N("m"),
        N("b")), Colon, Call("Matrix", Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal,
        Call("diagonal", Seq(N("i"), Mapsto, Parenthesized(new Formula.Power(Parenthesized(Call("asReal", new
        Formula.Negate(D(1)))), new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add,
        Parenthesized(Call("val", N("i"))))))))))));

    private static Formula F2() =>
        Disp(All("m", N("Nat"), All("a", new Formula.TypeArrow(Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")), All("e", new Formula.TypeArrow(Call("Fin", new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")), All("d",
        new Formula.TypeArrow(Call("Fin", new Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")), All("X", Call("Matrix", Call("Fin", new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")), All("Z",
        Call("Matrix", Call("Fin", new Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), Call("Fin", new Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")), new Formula.Logic(Parenthesized(All("t", Call("Fin", N("m")), new
        Formula.Relation(new Formula.Apply(N("e"), [Call("castSucc", N("t"))]), FormulaRelationOperator.NotEqual,
        D(0)))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("jacobiMatrix", N("m"), N("a"), N("e"))), FormulaBinaryOperator.Multiply,
        Parenthesized(N("X"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(N("X")),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("diagonal", N("d")))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("jacobiMatrix", N("m"), N("a"), N("e"))), FormulaBinaryOperator.Multiply,
        Parenthesized(N("Z"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(N("Z")),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("diagonal", N("d")))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(Call("transpose", N("X")),
        FormulaRelationOperator.Equal, N("X"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(Call("transpose", N("Z")), FormulaRelationOperator.Equal,
        N("Z"))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Apply(N("X"), [Call("Finlast", N("m")), Call("Finlast", N("m"))]), FormulaRelationOperator.Equal, new
        Formula.Apply(N("Z"), [Call("Finlast", N("m")), Call("Finlast", N("m"))]))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(N("X"), FormulaRelationOperator.Equal, N("Z")))))))))))))))))))));

    private static Formula F3() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new Formula.Relation(Call("asReal",
        Call("physicalC0", N("n"), N("j"), N("l"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("div", Call("asReal",
        Call("real", N("n"))), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", Call("asReal", Call("real", N("n"))), D(2))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Add, Parenthesized(Call("casimir",
        N("j"))))), FormulaBinaryOperator.Add, Parenthesized(Call("casimir", N("l")))))))));

    private static Formula F4() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalX", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("physicalU", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("indexParity", Call("channelWidth", N("n"), N("j"), N("l")), new
        Formula.Binary(Parenthesized(N("l")), FormulaBinaryOperator.Subtract, Parenthesized(N("j"))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("transpose", Call("physicalU", N("n"), N("j"),
        N("l"))))))))));

    private static Formula F5() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalM", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("smul", Call("physicalC0", N("n"), N("j"), N("l")), D(1))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("diagonal", Call("physicalCasimir", N("n"), N("j"),
        N("l")))))), FormulaBinaryOperator.Subtract, Parenthesized(Call("physicalT", N("n"), N("j"), N("l")))))))));

    private static Formula F6() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalV", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, Call("finiteSixJMatrix", N("n"), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("l"))), N("n"), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))),
        Call("channelBase", N("n"), N("j"), N("l")), Call("channelWidth", N("n"), N("j"), N("l")), Seq(N("h"), Colon,
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Mapsto, Parenthesized(Call("channelLabel", N("n"), N("j"),
        N("l"), Call("val", N("h")))))))))));

    private static Formula F7() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalTprime", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, Call("finiteSixJJacobi", N("n"), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("l"))), N("n"), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))),
        Call("channelBase", N("n"), N("j"), N("l")), Call("channelWidth", N("n"), N("j"), N("l"))))))));

    private static Formula F8() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalZ", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, Call("smul", new
        Formula.Power(Parenthesized(Call("asReal", new Formula.Negate(D(1)))), Call("channelBase", N("n"), N("j"),
        N("l"))), new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("indexParity",
        Call("channelWidth", N("n"), N("j"), N("l")), D(0))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("physicalV", N("n"), N("j"), N("l"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("indexParity", Call("channelWidth", N("n"), N("j"), N("l")), D(0))))))))));
}
