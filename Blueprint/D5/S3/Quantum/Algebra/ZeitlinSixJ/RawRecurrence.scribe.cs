using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class RawRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FluidDynamics/lichtenfelz2026zeitlin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J RawRecurrence"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. RacahOffsetse denotes the qualified projection RacahOffsets.e. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("four_spin_raw_recurrence", "four spin raw recurrence", F0(),
                "The zero-extended factorial terms satisfy a WZ identity. Summing its exact flux with both boundary values zero gives this four-spin recurrence.", DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("racahOffsets", "racahOffsets", F1(),
                "The displayed equation is the defining expression of racahOffsets.", DescribeRole.Definition, AssessedProvenance.FromRepo()),

            Node("racahSum_recurrence", "racahSum recurrence", F3(),
                "The four-spin recurrence acts on the actual Racah sums. The two neighboring labels are y+2 and y-2 because labels are doubled spins.", DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)),
            Node("zeroOffsets", "zeroOffsets", F4(),
                "The displayed equation is the defining expression of zeroOffsets.", DescribeRole.Definition, AssessedProvenance.FromRepo()),


            Node("spinCasimir", "spinCasimir", F7(),
                "The displayed equation is the defining expression of spinCasimir.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jacobiDenominator", "jacobiDenominator", F8(),
                "The displayed equation is the defining expression of jacobiDenominator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("pivotLeftNumerator", "pivotLeftNumerator", F9(),
                "The displayed equation is the defining expression of pivotLeftNumerator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("pivotRightNumerator", "pivotRightNumerator", F10(),
                "The displayed equation is the defining expression of pivotRightNumerator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("pivotLeft", "pivotLeft", F11(),
                "The displayed equation is the defining expression of pivotLeft.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("pivotRight", "pivotRight", F12(),
                "The displayed equation is the defining expression of pivotRight.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("endpointKernel", "endpointKernel", F13(),
                "The displayed equation is the defining expression of endpointKernel.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("endpointBase", "endpointBase", F14(),
                "The displayed equation is the defining expression of endpointBase.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("endpointConstant", "endpointConstant", F15(),
                "The displayed equation is the defining expression of endpointConstant.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("signedEndpointConstant", "signedEndpointConstant", F16(),
                "The displayed equation is the defining expression of signedEndpointConstant.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("endpointWeight", "endpointWeight", F17(),
                "The displayed equation is the defining expression of endpointWeight.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("signedEndpointWeight", "signedEndpointWeight", F18(),
                "The displayed equation is the defining expression of signedEndpointWeight.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("endpointFlux", "endpointFlux", F19(),
                "The displayed equation is the defining expression of endpointFlux.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("signedEndpointFlux", "signedEndpointFlux", F20(),
                "The displayed equation is the defining expression of signedEndpointFlux.", DescribeRole.Definition, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-rawrecurrence-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("q", N("RacahOffsets"), All("a", N("Rat"), All("b", N("Rat"), All("c", N("Rat"), All("d", N("Rat"),
        All("u", N("Rat"), All("y", N("Rat"), new Formula.Logic(Parenthesized(Call("compatible", N("q"), N("a"),
        N("b"), N("c"), N("d"), N("u"), N("y"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, Call("tc",
        N("q")))), FormulaLogicOperator.Implies, Parenthesized(All("e", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(Call("RacahOffsetse", N("q")), FormulaRelationOperator.Equal, Call("asInt", Call("int",
        N("e"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Relation(N("y"), FormulaRelationOperator.NotEqual, D(0))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.NotEqual, D(0))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("y")))), FormulaBinaryOperator.Add, Parenthesized(D(1))), FormulaRelationOperator.NotEqual,
        D(0))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("rawAlpha", N("a"), N("b"), N("c"), N("d"),
        N("y"))), FormulaBinaryOperator.Multiply, Parenthesized(Seq(Sum, Underscore, Grp(Seq(N("z"), InMacro,
        Call("range", new Formula.Binary(Parenthesized(N("e")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        Parenthesized(Call("offsetTerm", Call("raise", N("q")), N("z"))))))), FormulaBinaryOperator.Add,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("rawDiagonal", N("a"),
        N("b"), N("c"), N("d"), N("y"))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(N("u")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("u")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Seq(Sum, Underscore, Grp(Seq(N("z"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(N("e")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        Parenthesized(Call("offsetTerm", N("q"), N("z"))))))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(Call("rawGamma", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Seq(Sum, Underscore, Grp(Seq(N("z"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(N("e")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        Parenthesized(Call("offsetTerm", Call("lower", N("q")), N("z")))))))), FormulaRelationOperator.Equal,
        D(0)))))))))))))))))))))));

    private static Formula F1() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("u", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y",
        N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("racahOffsets", N("a"), N("b"), N("u"), N("c"), N("d"),
        N("y")), Colon, N("RacahOffsets"))), FormulaRelationOperator.Equal, Call("mk", Call("asInt", Call("int",
        Call("asNat", Call("natDiv", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("d")))), FormulaBinaryOperator.Add, Parenthesized(N("y"))),
        D(2))))), Call("asInt", Call("int", Call("asNat", Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("c")), FormulaBinaryOperator.Add, Parenthesized(N("b")))),
        FormulaBinaryOperator.Add, Parenthesized(N("y"))), D(2))))), Call("asInt", Call("int", Call("asNat",
        Call("natDiv", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("b")))), FormulaBinaryOperator.Add, Parenthesized(N("u"))),
        D(2))))), Call("asInt", Call("int", Call("asNat", Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("c")), FormulaBinaryOperator.Add, Parenthesized(N("d")))),
        FormulaBinaryOperator.Add, Parenthesized(N("u"))), D(2))))), Call("asInt", Call("int", Call("asNat",
        Call("natDiv", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b")))),
        FormulaBinaryOperator.Add, Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(N("d"))),
        D(2))))), Call("asInt", Call("int", Call("asNat", Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("u")), FormulaBinaryOperator.Add,
        Parenthesized(N("a")))), FormulaBinaryOperator.Add, Parenthesized(N("y")))), FormulaBinaryOperator.Add,
        Parenthesized(N("c"))), D(2))))), Call("asInt", Call("int", Call("asNat", Call("natDiv", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("b")),
        FormulaBinaryOperator.Add, Parenthesized(N("u")))), FormulaBinaryOperator.Add, Parenthesized(N("d")))),
        FormulaBinaryOperator.Add, Parenthesized(N("y"))), D(2))))))))))))));

    private static Formula F3() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("u", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("y",
        N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual,
        N("y"))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(Call("admissible",
        N("a"), N("b"), N("u"), N("c"), N("d"), N("y"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("rawAlpha", Call("div", Call("asRat", Call("rat", N("a"))), D(2)),
        Call("div", Call("asRat", Call("rat", N("b"))), D(2)), Call("div", Call("asRat", Call("rat", N("c"))), D(2)),
        Call("div", Call("asRat", Call("rat", N("d"))), D(2)), Call("div", Call("asRat", Call("rat", N("y"))),
        D(2)))), FormulaBinaryOperator.Multiply, Parenthesized(Call("racahSum", N("a"), N("b"), N("u"), N("c"),
        N("d"), new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(2))))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("rawDiagonal", Call("div", Call("asRat", Call("rat", N("a"))), D(2)),
        Call("div", Call("asRat", Call("rat", N("b"))), D(2)), Call("div", Call("asRat", Call("rat", N("c"))), D(2)),
        Call("div", Call("asRat", Call("rat", N("d"))), D(2)), Call("div", Call("asRat", Call("rat", N("y"))),
        D(2)))), FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(Call("div",
        Call("asRat", Call("rat", N("u"))), D(2))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", N("u"))), D(2))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("racahSum", N("a"), N("b"), N("u"), N("c"), N("d"), N("y"))))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(Call("rawGamma", Call("div",
        Call("asRat", Call("rat", N("a"))), D(2)), Call("div", Call("asRat", Call("rat", N("b"))), D(2)), Call("div",
        Call("asRat", Call("rat", N("c"))), D(2)), Call("div", Call("asRat", Call("rat", N("d"))), D(2)), Call("div",
        Call("asRat", Call("rat", N("y"))), D(2)))), FormulaBinaryOperator.Multiply, Parenthesized(Call("racahSum",
        N("a"), N("b"), N("u"), N("c"), N("d"), new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(2)))))))), FormulaRelationOperator.Equal, D(0)))))))))))));

    private static Formula F4() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("q", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("zeroOffsets", N("a"), N("b"), N("q")), Colon, N("RacahOffsets"))),
        FormulaRelationOperator.Equal, Call("mk", Call("asInt", Call("int", N("a"))), Call("asInt", Call("int", N("b"))), Call("asInt", Call("int", N("q"))), Call("asInt", Call("int", N("q"))), Call("asInt", Call("int",
        Call("asNat", new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b")))))),
        Call("asInt", Call("int", N("q"))), Call("asInt", Call("int", N("q")))))))));

    private static Formula F7() =>
        Disp(All("x", N("Rat"), new Formula.Relation(Call("asRat", Call("spinCasimir", N("x"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(N("x")), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(N("x")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))));

    private static Formula F8() =>
        Disp(All("k", N("Rat"), new Formula.Relation(Call("asRat", Call("jacobiDenominator", N("k"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("k")))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("k")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("k")))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))));

    private static Formula F9() =>
        Disp(All("s", N("Rat"), All("j", N("Rat"), All("l", N("Rat"), All("k", N("Rat"), new
        Formula.Relation(Call("asRat", Call("pivotLeftNumerator", N("s"), N("j"), N("l"), N("k"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("spinCasimir", N("l"))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("spinCasimir", new Formula.Binary(Parenthesized(N("k")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("s"))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("spinCasimir", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("k")), FormulaBinaryOperator.Add, Parenthesized(N("s")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("spinCasimir", N("j"))))))))))));

    private static Formula F10() =>
        Disp(All("s", N("Rat"), All("j", N("Rat"), All("l", N("Rat"), All("k", N("Rat"), new
        Formula.Relation(Call("asRat", Call("pivotRightNumerator", N("s"), N("j"), N("l"), N("k"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("spinCasimir", N("l"))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("spinCasimir", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("k")),
        FormulaBinaryOperator.Subtract, Parenthesized(N("s")))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("spinCasimir", new Formula.Binary(Parenthesized(N("k")),
        FormulaBinaryOperator.Add, Parenthesized(N("s"))))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("spinCasimir", N("j"))))))))))));

    private static Formula F11() =>
        Disp(All("s", N("Rat"), All("j", N("Rat"), All("l", N("Rat"), All("k", N("Rat"), new
        Formula.Relation(Call("asRat", Call("pivotLeft", N("s"), N("j"), N("l"), N("k"))),
        FormulaRelationOperator.Equal, Call("div", Call("pivotLeftNumerator", N("s"), N("j"), N("l"), N("k")), new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(N("k")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("k")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))))))));

    private static Formula F12() =>
        Disp(All("s", N("Rat"), All("j", N("Rat"), All("l", N("Rat"), All("k", N("Rat"), new
        Formula.Relation(Call("asRat", Call("pivotRight", N("s"), N("j"), N("l"), N("k"))),
        FormulaRelationOperator.Equal, Call("div", Call("pivotRightNumerator", N("s"), N("j"), N("l"), N("k")), new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("k")))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("k")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))))))));

    private static Formula F13() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), All("i", N("Nat"), new
        Formula.Relation(Call("asRat", Call("endpointKernel", N("n"), N("p"), N("d"), N("i"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("rat",
        Call("Natfactorial", new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(N("d")))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("n")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("int", N("i")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial",
        new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("p")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("int", N("i")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial",
        new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("i")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("int", N("d")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial",
        new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("n")))),
        FormulaBinaryOperator.Add, Parenthesized(Call("int", N("i"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("p")))),
        FormulaBinaryOperator.Add, Parenthesized(Call("int", N("i"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))))))));

    private static Formula F14() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), All("i", N("Nat"), new
        Formula.Relation(Call("asRat", Call("endpointBase", N("n"), N("p"), N("d"), N("i"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("rat",
        Call("Natfactorial", new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(N("d")))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("n")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("i")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("p")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("int", N("i")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial",
        new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("i")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("d")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("n")))),
        FormulaBinaryOperator.Add, Parenthesized(Call("int", N("i"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(2))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("p")))),
        FormulaBinaryOperator.Add, Parenthesized(Call("int", N("i"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))))))));

    private static Formula F15() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), new Formula.Relation(Call("asRat",
        Call("endpointConstant", N("n"), N("p"), N("d"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("rat",
        Call("Natfactorial", new Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("d")))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial",
        N("p")))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("p")), FormulaBinaryOperator.Subtract, Parenthesized(N("d")))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", N("n")))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Add,
        Parenthesized(N("p")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("invFactorial", Call("int", N("d")))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("n")))), FormulaBinaryOperator.Add,
        Parenthesized(Call("int", N("p"))))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("d"))))))))))));

    private static Formula F16() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), new Formula.Relation(Call("asRat",
        Call("signedEndpointConstant", N("n"), N("p"), N("d"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Subtract, Parenthesized(N("d")))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("p")), FormulaBinaryOperator.Subtract, Parenthesized(N("d")))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Add,
        Parenthesized(N("p")))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))))));

    private static Formula F17() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), All("i", N("Nat"), new
        Formula.Relation(Call("asRat", Call("endpointWeight", N("n"), N("p"), N("d"), N("i"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("endpointConstant", N("n"), N("p"), N("d"))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("asRat", Call("rat",
        N("i")))))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("endpointKernel", N("n"), N("p"), N("d"), N("i"))))))))));

    private static Formula F18() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), All("i", N("Nat"), new
        Formula.Relation(Call("asRat", Call("signedEndpointWeight", N("n"), N("p"), N("d"), N("i"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new Formula.Negate(D(1))), N("i"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("signedEndpointConstant", N("n"), N("p"), N("d"))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("asRat", Call("rat",
        N("i")))))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("endpointKernel", N("n"), N("p"), N("d"), N("i"))))))))));

    private static Formula F19() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), All("i", N("Nat"), new
        Formula.Relation(Call("asRat", Call("endpointFlux", N("n"), N("p"), N("d"), N("i"))),
        FormulaRelationOperator.Equal, Call("div", new Formula.Negate(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("i")))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("i")))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", N("d"))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat",
        N("p")))), FormulaBinaryOperator.Add, Parenthesized(Call("rat", N("i"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("n")))), FormulaBinaryOperator.Add,
        Parenthesized(Call("rat", N("i"))))), FormulaBinaryOperator.Add, Parenthesized(D(2)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("endpointConstant", new
        Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Add, Parenthesized(D(1))), N("p"), N("d"))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("endpointKernel", new Formula.Binary(Parenthesized(N("n")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), N("p"), N("d"), N("i"))))), new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("n")))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", N("d"))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat",
        N("n")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat",
        N("n")))), FormulaBinaryOperator.Add, Parenthesized(Call("rat", N("p"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(2))))))))))));

    private static Formula F20() =>
        Disp(All("n", N("Nat"), All("p", N("Nat"), All("d", N("Nat"), All("i", N("Nat"), new
        Formula.Relation(Call("asRat", Call("signedEndpointFlux", N("n"), N("p"), N("d"), N("i"))),
        FormulaRelationOperator.Equal, Call("div", new Formula.Negate(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new Formula.Negate(D(1))), N("i"))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat",
        N("i")))), FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", N("d"))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("p")))), FormulaBinaryOperator.Add,
        Parenthesized(Call("rat", N("i"))))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("n")))), FormulaBinaryOperator.Add,
        Parenthesized(Call("rat", N("i"))))), FormulaBinaryOperator.Add, Parenthesized(D(2)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("signedEndpointConstant", new
        Formula.Binary(Parenthesized(N("n")), FormulaBinaryOperator.Add, Parenthesized(D(1))), N("p"), N("d"))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("endpointKernel", new Formula.Binary(Parenthesized(N("n")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), N("p"), N("d"), N("i"))))), new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asRat",
        Call("rat", N("n")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("rat", N("d"))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("n")))),
        FormulaBinaryOperator.Add, Parenthesized(Call("rat", N("p"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(2))))))))))));


}
