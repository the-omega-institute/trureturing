using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FluidDynamics/lichtenfelz2026zeitlin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J Recurrence"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("channelLabel", "channelLabel", F0(),
                "The displayed equation is the defining expression of channelLabel.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("upperBand", "upperBand", F1(),
                "The displayed equation is the defining expression of upperBand.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("jacobiMatrix", "jacobiMatrix", F2(),
                "The displayed equation is the defining expression of jacobiMatrix.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalU", "physicalU", F3(),
                "The displayed equation is the defining expression of physicalU.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("normalizedSixJ", "normalizedSixJ", F4(),
                "The displayed equation is the defining expression of normalizedSixJ.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("normalizedUpper", "normalizedUpper", F5(),
                "The displayed equation is the defining expression of normalizedUpper.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("recurrenceDiagonalQ", "recurrenceDiagonalQ", F6(),
                "The displayed equation is the defining expression of recurrenceDiagonalQ.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("finiteSixJMatrix", "finiteSixJMatrix", F7(),
                "The displayed equation is the defining expression of finiteSixJMatrix.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("finiteSixJJacobi", "finiteSixJJacobi", F8(),
                "The displayed equation is the defining expression of finiteSixJJacobi.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("finiteSixJ_action", "finiteSixJ action", F9(),
                "The triangle-normalized Racah recurrence gives the finite Jacobi action. The zero, half-spin and interior cases and both omitted edges are all included.", DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-recurrence-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), All("t", N("Nat"), new
        Formula.Relation(Call("asNat", Call("channelLabel", N("n"), N("j"), N("l"), N("t"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(Call("channelBase", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("t")))))))))));

    private static Formula F1() =>
        Disp(All("m", N("Nat"), All("e", new Formula.TypeArrow(Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")), new
        Formula.Relation(Parenthesized(Seq(Call("upperBand", N("m"), N("e")), Colon, Call("Matrix", Call("Fin", new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")))),
        FormulaRelationOperator.Equal, Seq(N("i"), N("j"), Mapsto, Parenthesized(Call("ite", new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("val", N("i"))), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.Equal, Call("val", N("j"))), new Formula.Apply(N("e"), [N("i")]), D(0))))))));

    private static Formula F2() =>
        Disp(All("m", N("Nat"), All("a", new Formula.TypeArrow(Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")), All("e", new Formula.TypeArrow(Call("Fin", new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")), new
        Formula.Relation(Parenthesized(Seq(Call("jacobiMatrix", N("m"), N("a"), N("e")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        Call("Fin", new Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        N("Real")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("Matrixdiagonal", N("a"))), FormulaBinaryOperator.Add,
        Parenthesized(Call("upperBand", N("m"), N("e"))))), FormulaBinaryOperator.Add, Parenthesized(Call("transpose",
        Call("upperBand", N("m"), N("e"))))))))));

    private static Formula F3() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalU", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, Seq(N("k"), N("i"), Mapsto,
        Parenthesized(new Formula.Binary(Parenthesized(Call("Realsqrt", new
        Formula.Binary(Parenthesized(Call("asReal", Call("real", Call("asNat", new
        Formula.Binary(Parenthesized(Call("channelLabel", N("n"), N("j"), N("l"), Call("val", N("k")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("asReal", Call("real", Call("asNat", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("l")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("j")))), FormulaBinaryOperator.Add, Parenthesized(Call("val", N("i"))))))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("sixJ", N("n"), N("n"), new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("l")), FormulaBinaryOperator.Subtract, Parenthesized(N("j")))),
        FormulaBinaryOperator.Add, Parenthesized(Call("val", N("i")))))), new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("l"))), Call("channelLabel", N("n"), N("j"), N("l"),
        Call("val", N("k")))))))))))));

    private static Formula F4() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("u", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y",
        N("Nat"), new Formula.Relation(Call("asReal", Call("normalizedSixJ", N("a"), N("b"), N("u"), N("c"), N("d"),
        N("y"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(Call("Realsqrt", new
        Formula.Binary(Parenthesized(Call("asReal", Call("real", Call("asNat", new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real", Call("asNat", new
        Formula.Binary(Parenthesized(N("u")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("sixJ", N("a"), N("b"), N("u"), N("c"), N("d"),
        N("y"))))))))))));

    private static Formula F5() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y", N("Nat"), new
        Formula.Relation(Call("asReal", Call("normalizedUpper", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, Call("div", new Formula.Binary(Parenthesized(Call("recurrenceUpperCoefficient",
        N("a"), N("b"), N("c"), N("d"), N("y"))), FormulaBinaryOperator.Multiply, Parenthesized(Call("Realsqrt",
        Call("asReal", Call("real", Call("asNat", new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))))), Call("Realsqrt", Call("asReal", Call("real", Call("asNat", new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(3)))))))))))))));

    private static Formula F6() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y", N("Nat"), new
        Formula.Relation(Call("asRat", Call("recurrenceDiagonalQ", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(N("y"), FormulaRelationOperator.Equal, D(0)),
        new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat",
        N("a"))), D(2))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("div",
        Call("asRat", Call("rat", N("a"))), D(2))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(Call("div", Call("asRat",
        Call("rat", N("b"))), D(2))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", N("b"))), D(2))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))), Call("rawDiagonal", Call("div", Call("asRat", Call("rat",
        N("a"))), D(2)), Call("div", Call("asRat", Call("rat", N("b"))), D(2)), Call("div", Call("asRat", Call("rat",
        N("c"))), D(2)), Call("div", Call("asRat", Call("rat", N("d"))), D(2)), Call("div", Call("asRat", Call("rat",
        N("y"))), D(2)))))))))));

    private static Formula F7() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("base", N("Nat"),
        All("m", N("Nat"), All("iota", N("Type"), All("us", new Formula.TypeArrow(N("iota"), N("Nat")), new
        Formula.Relation(Parenthesized(Seq(Call("finiteSixJMatrix", N("a"), N("b"), N("c"), N("d"), N("base"), N("m"),
        N("iota"), N("us")), Colon, Call("Matrix", Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("iota"), N("Real")))), FormulaRelationOperator.Equal,
        Seq(N("k"), N("i"), Mapsto, Parenthesized(Call("normalizedSixJ", N("a"), N("b"), new Formula.Apply(N("us"),
        [N("i")]), N("c"), N("d"), new Formula.Binary(Parenthesized(N("base")), FormulaBinaryOperator.Add,
        Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("val", N("k")))))))))))))))))));

    private static Formula F8() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("base", N("Nat"),
        All("m", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("finiteSixJJacobi", N("a"), N("b"), N("c"),
        N("d"), N("base"), N("m")), Colon, Call("Matrix", Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal,
        Call("jacobiMatrix", N("m"), Seq(N("k"), Mapsto, Parenthesized(Call("asReal", Call("real",
        Call("recurrenceDiagonalQ", N("a"), N("b"), N("c"), N("d"), new Formula.Binary(Parenthesized(N("base")),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("val", N("k"))))))))))), Seq(N("k"), Mapsto,
        Parenthesized(Call("normalizedUpper", N("a"), N("b"), N("c"), N("d"), new
        Formula.Binary(Parenthesized(N("base")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("val",
        N("k"))))))))))))))))));

    private static Formula F9() =>
        Disp(All("iota", N("Type"), Seq(OpenBracket, Call("Fintype", N("iota")), CloseBracket, Comma, Seq(OpenBracket,
        Call("DecidableEq", N("iota")), CloseBracket, Comma, All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"),
        All("d", N("Nat"), All("base", N("Nat"), All("m", N("Nat"), All("us", new Formula.TypeArrow(N("iota"),
        N("Nat")), new Formula.Logic(Parenthesized(All("k", Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), All("i", N("iota"), Call("admissible", N("a"), N("b"), new
        Formula.Apply(N("us"), [N("i")]), N("c"), N("d"), new Formula.Binary(Parenthesized(N("base")),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("val", N("k")))))))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(All("i", N("iota"), new Formula.Logic(Parenthesized(new
        Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, N("base"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(Call("normalizedSixJ", N("a"), N("b"), new Formula.Apply(N("us"),
        [N("i")]), N("c"), N("d"), new Formula.Binary(Parenthesized(N("base")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(2)))), FormulaRelationOperator.Equal, D(0)))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(All("i", N("iota"), new Formula.Relation(Call("normalizedSixJ",
        N("a"), N("b"), new Formula.Apply(N("us"), [N("i")]), N("c"), N("d"), new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("base")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("m")))))),
        FormulaBinaryOperator.Add, Parenthesized(D(2)))), FormulaRelationOperator.Equal, D(0)))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("finiteSixJJacobi", N("a"), N("b"), N("c"), N("d"), N("base"), N("m"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("finiteSixJMatrix", N("a"), N("b"), N("c"), N("d"),
        N("base"), N("m"), N("us")))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("finiteSixJMatrix", N("a"), N("b"), N("c"), N("d"), N("base"), N("m"),
        N("us"))), FormulaBinaryOperator.Multiply, Parenthesized(Call("diagonal", Seq(N("i"), Mapsto,
        Parenthesized(Call("asReal", Call("real", Call("asRat", new Formula.Binary(Parenthesized(Call("div",
        Call("asRat", Call("rat", new Formula.Apply(N("us"), [N("i")]))), D(2))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", new
        Formula.Apply(N("us"), [N("i")]))), D(2))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))))))))))))))))))))))))))));
}
