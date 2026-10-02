using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class ExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FluidDynamics/lichtenfelz2026zeitlin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J Expansion"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("racah_expansion_open", "racah expansion open", F0(),
                "The normalized Wigner symbol equals the terminating Racah polynomial. The recurrence and zero-row initial value identify the two sequences over the full finite range.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("rawAlpha", "rawAlpha", F1(),
                "The displayed equation is the defining expression of rawAlpha.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("rawGamma", "rawGamma", F2(),
                "The displayed equation is the defining expression of rawGamma.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("rawDiagonal", "rawDiagonal", F3(),
                "The displayed equation is the defining expression of rawDiagonal.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fourSpinDenominator", "fourSpinDenominator", F4(),
                "The displayed equation is the defining expression of fourSpinDenominator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fourSpinCertificateNumerator", "fourSpinCertificateNumerator", F5(),
                "The displayed equation is the defining expression of fourSpinCertificateNumerator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fourSpinCertificate", "fourSpinCertificate", F6(),
                "The displayed equation is the defining expression of fourSpinCertificate.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("compressedAlpha", "compressedAlpha", F7(),
                "The displayed equation is the defining expression of compressedAlpha.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("compressedBeta", "compressedBeta", F8(),
                "The displayed equation is the defining expression of compressedBeta.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("compressedGamma", "compressedGamma", F9(),
                "The displayed equation is the defining expression of compressedGamma.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("compressedV", "compressedV", F10(),
                "The displayed equation is the defining expression of compressedV.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("compressedZ", "compressedZ", F11(),
                "The displayed equation is the defining expression of compressedZ.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("compressedQ", "compressedQ", F12(),
                "The displayed equation is the defining expression of compressedQ.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("compressedCertificate", "compressedCertificate", F13(),
                "The displayed equation is the defining expression of compressedCertificate.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("RacahOffsets", "RacahOffsets", F14(),
                "The displayed equation is the defining expression of RacahOffsets.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("RacahOffsets.raise", "Offsets raise", F15(),
                "The displayed equation is the defining expression of RacahOffsets.raise.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("RacahOffsets.lower", "Offsets lower", F16(),
                "The displayed equation is the defining expression of RacahOffsets.lower.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("offsetTerm", "offsetTerm", F17(),
                "The displayed equation is the defining expression of offsetTerm.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("offsetBase", "offsetBase", F18(),
                "The displayed equation is the defining expression of offsetBase.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("offsetFlux", "offsetFlux", F19(),
                "The displayed equation is the defining expression of offsetFlux.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("RacahOffsets.compatible", "Offsets compatible", F20(),
                "The displayed equation is the defining expression of RacahOffsets.compatible.", DescribeRole.Definition, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-expansion-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("N", N("Nat"), All("i", N("Nat"), All("j", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, N("N"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(N("i"), FormulaRelationOperator.LessThan,
        N("N"))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", new Formula.Negate(D(1)))), new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))), FormulaBinaryOperator.Add, Parenthesized(N("i")))), FormulaBinaryOperator.Add,
        Parenthesized(N("j"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("real", N("N"))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("Wij", N("N"), N("i"), N("j")))),
        FormulaRelationOperator.Equal, Call("asReal", Call("real", Call("racahPolynomial", N("N"), N("j"),
        N("i")))))))))))))));

    private static Formula F1() =>
        Disp(All("a", N("Rat"), All("b", N("Rat"), All("c", N("Rat"), All("d", N("Rat"), All("y", N("Rat"), new
        Formula.Relation(Call("asRat", Call("rawAlpha", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, Call("div", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("d")))), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("c")))), D(2)))))), new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("y")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))))))));

    private static Formula F2() =>
        Disp(All("a", N("Rat"), All("b", N("Rat"), All("c", N("Rat"), All("d", N("Rat"), All("y", N("Rat"), new
        Formula.Relation(Call("asRat", Call("rawGamma", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, Call("div", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("d")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Power(Parenthesized(N("y")), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add, Parenthesized(N("c")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Power(Parenthesized(N("y")), D(2)))))), new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("y")))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("y")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))))))))));

    private static Formula F3() =>
        Disp(All("a", N("Rat"), All("b", N("Rat"), All("c", N("Rat"), All("d", N("Rat"), All("y", N("Rat"), new
        Formula.Relation(Call("asRat", Call("rawDiagonal", N("a"), N("b"), N("c"), N("d"), N("y"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(N("b")),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("b")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("div", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(N("d")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("d")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(N("b")),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("b")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(N("c")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("c")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))), new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("y")))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))))))))));

    private static Formula F4() =>
        Disp(All("y", N("Rat"), new Formula.Relation(Call("asRat", Call("fourSpinDenominator", N("y"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("y")))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("y")))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))));

    private static Formula F5() =>
        Disp(All("a", N("Rat"), All("b", N("Rat"), All("c", N("Rat"), All("d", N("Rat"), All("u", N("Rat"), All("y",
        N("Rat"), All("z", N("Rat"), new Formula.Relation(Call("asRat", Call("fourSpinCertificateNumerator", N("a"),
        N("b"), N("c"), N("d"), N("u"), N("y"), N("z"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Negate(new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add,
        Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Subtract,
        Parenthesized(N("y")))))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add,
        Parenthesized(N("d")))), FormulaBinaryOperator.Add, Parenthesized(N("y")))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("b")))), FormulaBinaryOperator.Add, Parenthesized(N("u")))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("d")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(N("u")))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))), FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("u")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("d")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add, Parenthesized(N("c")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Power(Parenthesized(N("y")), D(2))))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Subtract, Parenthesized(N("b")))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("c")), FormulaBinaryOperator.Subtract, Parenthesized(N("d")))))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Power(Parenthesized(new
        Formula.Binary(Parenthesized(N("u")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))))))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("z")),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add, Parenthesized(N("c")))),
        FormulaBinaryOperator.Add, Parenthesized(N("y")))))))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("u")))), FormulaBinaryOperator.Multiply, Parenthesized(N("y")))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Power(Parenthesized(N("y")), D(2))))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("d")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add, Parenthesized(N("c")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("a")))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("b")))), FormulaBinaryOperator.Multiply, Parenthesized(N("d")))))), FormulaBinaryOperator.Add,
        Parenthesized(N("a")))), FormulaBinaryOperator.Add, Parenthesized(N("b")))), FormulaBinaryOperator.Add,
        Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(N("d")))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("z")),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add, Parenthesized(N("c")))),
        FormulaBinaryOperator.Add, Parenthesized(N("y")))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add,
        Parenthesized(N("d")))), FormulaBinaryOperator.Add, Parenthesized(N("y"))))))))))))))))));

    private static Formula F6() =>
        Disp(All("a", N("Rat"), All("b", N("Rat"), All("c", N("Rat"), All("d", N("Rat"), All("u", N("Rat"), All("y",
        N("Rat"), All("z", N("Rat"), new Formula.Relation(Call("asRat", Call("fourSpinCertificate", N("a"), N("b"),
        N("c"), N("d"), N("u"), N("y"), N("z"))), FormulaRelationOperator.Equal, Call("div",
        Call("fourSpinCertificateNumerator", N("a"), N("b"), N("c"), N("d"), N("u"), N("y"), N("z")),
        Call("fourSpinDenominator", N("y"))))))))))));

    private static Formula F7() =>
        Disp(All("h", N("Rat"), All("v", N("Rat"), All("p", N("Rat"), All("q", N("Rat"), All("y", N("Rat"), new
        Formula.Relation(Call("asRat", Call("compressedAlpha", N("h"), N("v"), N("p"), N("q"), N("y"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(N("p")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("q")))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("v")), FormulaBinaryOperator.Subtract,
        Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("y")))))), FormulaBinaryOperator.Subtract, Parenthesized(D(2)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("p")),
        FormulaBinaryOperator.Subtract, Parenthesized(N("q")))))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(4)), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2))))), FormulaBinaryOperator.Multiply,
        Parenthesized(N("q"))))))))))))));

    private static Formula F8() =>
        Disp(All("m", N("Rat"), All("h", N("Rat"), All("v", N("Rat"), All("p", N("Rat"), All("q", N("Rat"), All("y",
        N("Rat"), new Formula.Relation(Call("asRat", Call("compressedBeta", N("m"), N("h"), N("v"), N("p"), N("q"),
        N("y"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Negate(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("y")))), FormulaBinaryOperator.Add, Parenthesized(D(1))))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("p")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("q")))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Multiply, Parenthesized(N("h")))))),
        FormulaBinaryOperator.Subtract, Parenthesized(N("y")))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("y")))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("p")))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("y")))), FormulaBinaryOperator.Multiply, Parenthesized(N("h")))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(D(1)),
        FormulaBinaryOperator.Subtract, Parenthesized(N("v")))))))))))))))));

    private static Formula F9() =>
        Disp(All("m", N("Rat"), All("h", N("Rat"), All("y", N("Rat"), new Formula.Relation(Call("asRat",
        Call("compressedGamma", N("m"), N("h"), N("y"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("y")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Multiply, Parenthesized(N("m")))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("y")))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("h"))))))))))));

    private static Formula F10() =>
        Disp(All("v", N("Rat"), All("p", N("Rat"), All("x", N("Rat"), new Formula.Relation(Call("asRat",
        Call("compressedV", N("v"), N("p"), N("x"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(N("x")), D(2))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(N("v")),
        FormulaBinaryOperator.Multiply, Parenthesized(N("x")))))), FormulaBinaryOperator.Add,
        Parenthesized(N("p"))))))));

    private static Formula F11() =>
        Disp(All("m", N("Rat"), All("h", N("Rat"), All("y", N("Rat"), All("x", N("Rat"), new
        Formula.Relation(Call("asRat", Call("compressedZ", N("m"), N("h"), N("y"), N("x"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("y")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(N("h")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("h")),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("y")))))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(2)))), FormulaBinaryOperator.Multiply, Parenthesized(N("x")))))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Power(Parenthesized(N("x")), D(2))))))))));

    private static Formula F12() =>
        Disp(All("v", N("Rat"), All("q", N("Rat"), All("y", N("Rat"), All("x", N("Rat"), new
        Formula.Relation(Call("asRat", Call("compressedQ", N("v"), N("q"), N("y"), N("x"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(N("x")), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("v")),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("y")))))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(2)))), FormulaBinaryOperator.Multiply, Parenthesized(N("x")))))), FormulaBinaryOperator.Add,
        Parenthesized(N("q")))))))));

    private static Formula F13() =>
        Disp(All("m", N("Rat"), All("h", N("Rat"), All("v", N("Rat"), All("p", N("Rat"), All("q", N("Rat"), All("y",
        N("Rat"), All("x", N("Rat"), new Formula.Relation(Call("asRat", Call("compressedCertificate", N("m"), N("h"),
        N("v"), N("p"), N("q"), N("y"), N("x"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Negate(new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1))))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("m")))), FormulaBinaryOperator.Multiply,
        Parenthesized(N("p")))), FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("v")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("h")))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("m")), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("y")))), FormulaBinaryOperator.Multiply, Parenthesized(N("h")))))))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("y")))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("p")))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(N("x")))))), FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("p")), FormulaBinaryOperator.Subtract, Parenthesized(N("q")))))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("m")))))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("y")))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("y")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(N("h")))))), FormulaBinaryOperator.Multiply,
        Parenthesized(N("x")))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("x")), FormulaBinaryOperator.Subtract, Parenthesized(N("h"))))))))))))))));

    private static Formula F14() =>
        Disp(Call("Structure", N("RacahOffsets"), Call("Fields", N("ta"), N("tb"), N("tc"), N("td"), N("e"), N("f"),
        N("g")), N("Int")));

    private static Formula F15() =>
        Disp(All("q", N("RacahOffsets"), new Formula.Relation(Parenthesized(Seq(Call("raise", N("q")), Colon,
        N("RacahOffsets"))), FormulaRelationOperator.Equal, Call("mk", new Formula.Binary(Parenthesized(Call("ta",
        N("q"))), FormulaBinaryOperator.Add, Parenthesized(D(1))), new Formula.Binary(Parenthesized(Call("tb",
        N("q"))), FormulaBinaryOperator.Add, Parenthesized(D(1))), Call("tc", N("q")), Call("td", N("q")), Call("e",
        N("q")), new Formula.Binary(Parenthesized(Call("f", N("q"))), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        new Formula.Binary(Parenthesized(Call("g", N("q"))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))));

    private static Formula F16() =>
        Disp(All("q", N("RacahOffsets"), new Formula.Relation(Parenthesized(Seq(Call("lower", N("q")), Colon,
        N("RacahOffsets"))), FormulaRelationOperator.Equal, Call("mk", new Formula.Binary(Parenthesized(Call("ta",
        N("q"))), FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new Formula.Binary(Parenthesized(Call("tb",
        N("q"))), FormulaBinaryOperator.Subtract, Parenthesized(D(1))), Call("tc", N("q")), Call("td", N("q")),
        Call("e", N("q")), new Formula.Binary(Parenthesized(Call("f", N("q"))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))), new Formula.Binary(Parenthesized(Call("g", N("q"))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))))));

    private static Formula F17() =>
        Disp(All("q", N("RacahOffsets"), All("z", N("Nat"), new Formula.Relation(Call("asRat", Call("offsetTerm",
        N("q"), N("z"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))),
        N("z"))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("ta", N("q")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("tb", N("q")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("tc", N("q")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("td", N("q")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("e", N("q"))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("z")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("f", N("q"))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("z")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("g", N("q"))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("z")))))))))));

    private static Formula F18() =>
        Disp(All("q", N("RacahOffsets"), All("z", N("Nat"), new Formula.Relation(Call("asRat", Call("offsetBase",
        N("q"), N("z"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))),
        N("z"))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("ta", N("q"))))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("tb", N("q"))))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("tc", N("q")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("td", N("q")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("e", N("q"))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("z")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("f", N("q"))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("z"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("g", N("q"))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("z"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))))));

    private static Formula F19() =>
        Disp(All("q", N("RacahOffsets"), All("P", new Formula.TypeArrow(N("Rat"), N("Rat")), All("z", N("Nat"), new
        Formula.Relation(Call("asRat", Call("offsetFlux", N("q"), N("P"), N("z"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))), N("z"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Apply(N("P"), [Call("asRat", Call("rat", N("z")))])))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("ta", N("q")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("tb", N("q")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("tc", N("q"))))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("z")))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("td", N("q"))))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("e", N("q"))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("z")))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("f", N("q"))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("z"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("g", N("q"))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("z"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))))))));

    private static Formula F20() =>
        Disp(All("q", N("RacahOffsets"), All("a", N("Rat"), All("b", N("Rat"), All("c", N("Rat"), All("d", N("Rat"),
        All("u", N("Rat"), All("y", N("Rat"), new Formula.Relation(Parenthesized(Seq(Call("compatible", N("q"),
        N("a"), N("b"), N("c"), N("d"), N("u"), N("y")), Colon, N("Prop"))), FormulaRelationOperator.Equal, new
        Formula.Logic(Parenthesized(new Formula.Relation(Call("asRat", Call("rat", Call("ta", N("q")))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("d")))), FormulaBinaryOperator.Add, Parenthesized(N("y"))))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(Call("asRat",
        Call("rat", Call("tb", N("q")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add, Parenthesized(N("c")))),
        FormulaBinaryOperator.Add, Parenthesized(N("y"))))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(Call("asRat", Call("rat", Call("tc", N("q")))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("b")))), FormulaBinaryOperator.Add, Parenthesized(N("u"))))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(Call("asRat",
        Call("rat", Call("td", N("q")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("c")), FormulaBinaryOperator.Add, Parenthesized(N("d")))),
        FormulaBinaryOperator.Add, Parenthesized(N("u"))))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(Call("asRat", Call("rat", Call("e", N("q")))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b")))),
        FormulaBinaryOperator.Add, Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(N("d"))))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(Call("asRat",
        Call("rat", Call("f", N("q")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add,
        Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(N("u")))), FormulaBinaryOperator.Add,
        Parenthesized(N("y"))))), FormulaLogicOperator.And, Parenthesized(new Formula.Relation(Call("asRat",
        Call("rat", Call("g", N("q")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add,
        Parenthesized(N("d")))), FormulaBinaryOperator.Add, Parenthesized(N("u")))), FormulaBinaryOperator.Add,
        Parenthesized(N("y")))))))))))))))))))))))));
}
