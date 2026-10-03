using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J Endpoint"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("endpoint_normalization", "endpoint normalization", F0(),
                "The stretched weights sum to one for every n at least d. The exact flux recurrence and the initial normalization give a finite induction.", DescribeRole.Lemma, AssessedProvenance.FromRepo()),

            Node("signed_stretched_endpoint_match", "signed stretched endpoint match", F2(),
                "The alternating squared stretched row equals the endpoint entry of the second Racah matrix, with the exact Racah phase.", DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("dual_intertwining_orthogonality", "dual intertwining orthogonality", F3(),
                "The two intertwining equations force the Gram matrix to commute with an injective diagonal and a connected Jacobi matrix. It is diagonal and its adjacent entries coincide; the endpoint normalization fixes them to one.", DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("jacobiEdgeSq", "jacobiEdgeSq", F4(),
                "The displayed equation is the defining expression of jacobiEdgeSq.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("triangleSqProduct", "triangleSqProduct", F5(),
                "The displayed equation is the defining expression of triangleSqProduct.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("raisingNumerator", "raisingNumerator", F6(),
                "The displayed equation is the defining expression of raisingNumerator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("raisingDenominator", "raisingDenominator", F7(),
                "The displayed equation is the defining expression of raisingDenominator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("recurrenceUpperCoefficient", "recurrenceUpperCoefficient", F8(),
                "The displayed equation is the defining expression of recurrenceUpperCoefficient.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("recurrenceLowerCoefficient", "recurrenceLowerCoefficient", F9(),
                "The displayed equation is the defining expression of recurrenceLowerCoefficient.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("channelWidth", "channelWidth", F10(),
                "The displayed equation is the defining expression of channelWidth.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("channelBase", "channelBase", F11(),
                "The displayed equation is the defining expression of channelBase.", DescribeRole.Definition, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-endpoint-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(N("d"), FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(N("d"),
        FormulaRelationOperator.LessThanOrEqual, N("p"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(N("p")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        Parenthesized(Call("endpointWeight", N("n"), N("p"), N("d"), N("i")))), FormulaRelationOperator.Equal,
        D(1))))))))));

    private static Formula F2() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("d", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(N("d"), FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("j")))), FormulaBinaryOperator.Add, Parenthesized(N("d")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", new Formula.Negate(D(1)))), N("i"))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asReal", Call("real", Call("asNat", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j")))))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("asReal", Call("real", N("i")))))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("sixJ", N("n"), N("n"), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("i"))), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(N("d"))))), new
        Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))))))), D(2)))))))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", new Formula.Negate(D(1)))), new
        Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real", Call("asNat", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Add,
        Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("j")))))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("sixJ", N("n"), new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Add, Parenthesized(N("d"))))), new Formula.Binary(Parenthesized(N("n")),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("j"))))), N("n"), new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new Formula.Binary(Parenthesized(N("n")),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("j")))))))))))))));

    private static Formula F3() =>
        Disp(All("iota", N("Type"), Seq(OpenBracket, Call("Fintype", N("iota")), CloseBracket, Comma, Seq(OpenBracket,
        Call("DecidableEq", N("iota")), CloseBracket, Comma, All("m", N("Nat"), All("U", Call("Matrix", Call("Fin",
        new Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("iota"),
        N("Real")), All("T", Call("Matrix", Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")), All("H", Call("Matrix", N("iota"), N("iota"),
        N("Real")), All("dk", new Formula.TypeArrow(Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")), All("li", new Formula.TypeArrow(N("iota"),
        N("Real")), new Formula.Logic(Parenthesized(Call("FunctionInjective", N("dk"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(Call("transpose", N("T")),
        FormulaRelationOperator.Equal, N("T"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(Call("transpose", N("H")), FormulaRelationOperator.Equal,
        N("H"))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(N("T")), FormulaBinaryOperator.Multiply, Parenthesized(N("U"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(N("U")), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("diagonal", N("li")))))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(Call("diagonal", N("dk"))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("U"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(N("U")), FormulaBinaryOperator.Multiply, Parenthesized(N("H"))))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(All("t", Call("Fin", N("m")), new
        Formula.Relation(new Formula.Apply(N("T"), [Call("castSucc", N("t")), Call("succ", N("t"))]),
        FormulaRelationOperator.NotEqual, D(0)))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(new Formula.Apply(new
        Formula.Binary(Parenthesized(N("U")), FormulaBinaryOperator.Multiply, Parenthesized(Call("transpose",
        N("U")))), [Call("Finlast", N("m"))]), [Call("Finlast", N("m"))]), FormulaRelationOperator.Equal, D(1))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(N("U")),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("transpose", N("U")))), FormulaRelationOperator.Equal,
        D(1))))))))))))))))))))))))));

    private static Formula F4() =>
        Disp(All("s", N("Rat"), All("j", N("Rat"), All("l", N("Rat"), All("k", N("Rat"), new
        Formula.Relation(Call("asRat", Call("jacobiEdgeSq", N("s"), N("j"), N("l"), N("k"))),
        FormulaRelationOperator.Equal, Call("div", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(N("k")), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(N("s")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("j")))), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("s")), FormulaBinaryOperator.Add, Parenthesized(N("j")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Power(Parenthesized(N("k")), D(2))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(N("k")), D(2))), FormulaBinaryOperator.Subtract,
        Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(N("s")),
        FormulaBinaryOperator.Subtract, Parenthesized(N("l")))), D(2))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("s")), FormulaBinaryOperator.Add,
        Parenthesized(N("l")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Power(Parenthesized(N("k")), D(2)))))), new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(4)),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(N("k")), D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("k")))),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("k")))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))))));

    private static Formula F5() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("u", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y",
        N("Nat"), new Formula.Relation(Call("asRat", Call("triangleSqProduct", N("a"), N("b"), N("u"), N("c"), N("d"),
        N("y"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("deltaSq", N("a"), N("b"), N("u"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("deltaSq", N("a"), N("d"), N("y"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("deltaSq", N("c"), N("b"), N("y"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("deltaSq", N("c"), N("d"), N("u"))))))))))));

    private static Formula F6() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y", N("Nat"), new
        Formula.Relation(Call("asRat", Call("raisingNumerator", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", N("y"))),
        D(2))), FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))), FormulaBinaryOperator.Subtract,
        Parenthesized(new Formula.Power(Parenthesized(Call("div", new Formula.Binary(Parenthesized(Call("asRat",
        Call("rat", N("a")))), FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", N("d")))), D(2))), D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", N("y"))),
        D(2))), FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))), FormulaBinaryOperator.Subtract,
        Parenthesized(new Formula.Power(Parenthesized(Call("div", new Formula.Binary(Parenthesized(Call("asRat",
        Call("rat", N("b")))), FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", N("c")))), D(2))),
        D(2)))))))))))));

    private static Formula F7() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y", N("Nat"), new
        Formula.Relation(Call("asRat", Call("raisingDenominator", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(Call("div", new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("a")))), FormulaBinaryOperator.Add,
        Parenthesized(Call("rat", N("d")))), D(2))), FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Power(Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", N("y"))), D(2))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(Call("div", new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("b")))), FormulaBinaryOperator.Add,
        Parenthesized(Call("rat", N("c")))), D(2))), FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Power(Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", N("y"))), D(2))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2)))))))))))));

    private static Formula F8() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y", N("Nat"), new
        Formula.Relation(Call("asReal", Call("recurrenceUpperCoefficient", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, Call("div", Call("Realsqrt", Call("asReal", Call("real", Call("asRat", new
        Formula.Binary(Parenthesized(Call("raisingNumerator", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("raisingDenominator", N("a"), N("b"), N("c"), N("d"),
        N("y")))))))), Call("asReal", Call("real", Call("asRat", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", N("y"))), D(2))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("div", Call("asRat", Call("rat", N("y"))), D(2))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))))))))))));

    private static Formula F9() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y", N("Nat"), new
        Formula.Relation(Call("asReal", Call("recurrenceLowerCoefficient", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, Call("div", Call("Realsqrt", Call("asReal", Call("real", Call("asRat", new
        Formula.Binary(Parenthesized(Call("raisingNumerator", N("a"), N("b"), N("c"), N("d"), new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Subtract, Parenthesized(D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("raisingDenominator", N("a"), N("b"), N("c"), N("d"), new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Subtract, Parenthesized(D(2)))))))))),
        Call("asReal", Call("real", Call("asRat", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("div", Call("asRat",
        Call("rat", N("y"))), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("div", Call("asRat", Call("rat", N("y"))), D(2))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))))))))))));

    private static Formula F10() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new Formula.Relation(Call("asNat",
        Call("channelWidth", N("n"), N("j"), N("l"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("min", N("n"), new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Add, Parenthesized(N("l"))))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(N("l")), FormulaBinaryOperator.Subtract, Parenthesized(N("j"))))))))));

    private static Formula F11() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new Formula.Relation(Call("asNat",
        Call("channelBase", N("n"), N("j"), N("l"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("max", N("n"), new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(N("l"))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("min", N("n"), new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Add, Parenthesized(N("l"))))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(N("l")), FormulaBinaryOperator.Subtract, Parenthesized(N("j"))))))))));
}
