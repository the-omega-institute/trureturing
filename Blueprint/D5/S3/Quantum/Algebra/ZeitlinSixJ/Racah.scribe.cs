using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class RacahDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FluidDynamics/lichtenfelz2026zeitlin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J Racah"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("triangle", "triangle", F0(),
                "The displayed equation is the defining expression of triangle.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("triangleDecidable", "triangleDecidable", F1(),
                "The displayed equation is the defining expression of triangleDecidable.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("admissible", "admissible", F2(),
                "The displayed equation is the defining expression of admissible.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("admissibleDecidable", "admissibleDecidable", F3(),
                "The displayed equation is the defining expression of admissibleDecidable.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("deltaSq", "deltaSq", F4(),
                "The displayed equation is the defining expression of deltaSq.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lower", "lower", F5(),
                "The displayed equation is the defining expression of lower.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("upper", "upper", F6(),
                "The displayed equation is the defining expression of upper.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("racahTerm", "racahTerm", F7(),
                "The displayed equation is the defining expression of racahTerm.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("racahSum", "racahSum", F8(),
                "The displayed equation is the defining expression of racahSum.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sixJ", "sixJ", F9(),
                "The displayed equation is the defining expression of sixJ.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("racahMonomial", "racahMonomial", F10(),
                "The displayed equation is the defining expression of racahMonomial.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("racahCoefficient", "racahCoefficient", F11(),
                "The displayed equation is the defining expression of racahCoefficient.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("racahPolynomial", "racahPolynomial", F12(),
                "The displayed equation is the defining expression of racahPolynomial.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("polynomial_harmonic", "polynomial harmonic", F13(),
                "The weighted terminating Racah polynomial sum equals twice the harmonic number. A finite antidifference and a binomial harmonic induction evaluate the sum.", DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("W", "W", F14(),
                "Page 6, section 2.2: “To begin, for fixed N, we introduce the abbreviated notation below for certain six-j symbols that appear frequently throughout the paper:”. The defining equation below implements equation (2.6). Each sixJ label is twice the displayed spin; W(N,i,j,l) denotes the symbol with top row i,j,l and bottom row (N−1)/2,(N−1)/2,(N−1)/2, and Wij(N,i,j) denotes the symbol with top row i,(N−1)/2,(N−1)/2 and bottom row j,(N−1)/2,(N−1)/2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Wij", "Wij", F15(),
                "Page 6, section 2.2: “To begin, for fixed N, we introduce the abbreviated notation below for certain six-j symbols that appear frequently throughout the paper:”. The defining equation below implements equation (2.6). Each sixJ label is twice the displayed spin; W(N,i,j,l) denotes the symbol with top row i,j,l and bottom row (N−1)/2,(N−1)/2,(N−1)/2, and Wij(N,i,j) denotes the symbol with top row i,(N−1)/2,(N−1)/2 and bottom row j,(N−1)/2,(N−1)/2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("casimir", "casimir", F16(),
                "The displayed equation is the defining expression of casimir.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("newtonBasis", "newtonBasis", F17(),
                "The displayed equation is the defining expression of newtonBasis.", DescribeRole.Definition, AssessedProvenance.FromRepo()),

            Node("recurrence_unique", "recurrence unique", F19(),
                "The forward coefficient does not vanish below N. Strong induction determines the whole finite sequence from its initial value and the difference equation.", DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("certificatePolynomial", "certificatePolynomial", F20(),
                "The displayed equation is the defining expression of certificatePolynomial.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("normalizedRacah", "normalizedRacah", F21(),
                "The displayed equation is the defining expression of normalizedRacah.", DescribeRole.Definition, AssessedProvenance.FromRepo()),

            Node("invFactorial", "invFactorial", F23(),
                "The displayed equation is the defining expression of invFactorial.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("factorialKernel", "factorialKernel", F24(),
                "The displayed equation is the defining expression of factorialKernel.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("certificateBase", "certificateBase", F25(),
                "The displayed equation is the defining expression of certificateBase.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("kernelFlux", "kernelFlux", F26(),
                "The displayed equation is the defining expression of kernelFlux.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("racahPrefactor", "racahPrefactor", F27(),
                "The displayed equation is the defining expression of racahPrefactor.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("kernelSequence", "kernelSequence", F28(),
                "The displayed equation is the defining expression of kernelSequence.", DescribeRole.Definition, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-racah-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("triangle", N("a"), N("b"), N("c")), Colon, N("Prop"))),
        FormulaRelationOperator.Equal, new Formula.Logic(Parenthesized(new Formula.Relation(N("a"),
        FormulaRelationOperator.LessThanOrEqual, new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add,
        Parenthesized(N("c"))))), FormulaLogicOperator.And, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Relation(N("b"), FormulaRelationOperator.LessThanOrEqual, new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("c"))))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(N("c"), FormulaRelationOperator.LessThanOrEqual, new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b"))))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(Call("mod", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b")))),
        FormulaBinaryOperator.Add, Parenthesized(N("c"))), D(2)), FormulaRelationOperator.Equal, D(0)))))))))))));

    private static Formula F1() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("triangleDecidable", N("a"), N("b"), N("c")), Colon, Call("Decidable",
        Call("triangle", N("a"), N("b"), N("c"))))), FormulaRelationOperator.Equal, Call("inferInstanceAs",
        Call("Decidable", new Formula.Logic(Parenthesized(new Formula.Relation(N("a"),
        FormulaRelationOperator.LessThanOrEqual, new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add,
        Parenthesized(N("c"))))), FormulaLogicOperator.And, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Relation(N("b"), FormulaRelationOperator.LessThanOrEqual, new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("c"))))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(N("c"), FormulaRelationOperator.LessThanOrEqual, new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b"))))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(Call("mod", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b")))),
        FormulaBinaryOperator.Add, Parenthesized(N("c"))), D(2)), FormulaRelationOperator.Equal, D(0)))))))))))))));

    private static Formula F2() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("e", N("Nat"), All("f",
        N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("admissible", N("a"), N("b"), N("c"), N("d"), N("e"),
        N("f")), Colon, N("Prop"))), FormulaRelationOperator.Equal, new Formula.Logic(Parenthesized(Call("triangle",
        N("a"), N("b"), N("c"))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(Call("triangle", N("a"), N("e"), N("f"))), FormulaLogicOperator.And,
        Parenthesized(new Formula.Logic(Parenthesized(Call("triangle", N("d"), N("b"), N("f"))),
        FormulaLogicOperator.And, Parenthesized(Call("triangle", N("d"), N("e"), N("c"))))))))))))))));

    private static Formula F3() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("e", N("Nat"), All("f",
        N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("admissibleDecidable", N("a"), N("b"), N("c"), N("d"),
        N("e"), N("f")), Colon, Call("Decidable", Call("admissible", N("a"), N("b"), N("c"), N("d"), N("e"),
        N("f"))))), FormulaRelationOperator.Equal, Call("inferInstanceAs", Call("Decidable", new
        Formula.Logic(Parenthesized(Call("triangle", N("a"), N("b"), N("c"))), FormulaLogicOperator.And,
        Parenthesized(new Formula.Logic(Parenthesized(Call("triangle", N("a"), N("e"), N("f"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Logic(Parenthesized(Call("triangle", N("d"), N("b"),
        N("f"))), FormulaLogicOperator.And, Parenthesized(Call("triangle", N("d"), N("e"), N("c"))))))))))))))))));

    private static Formula F4() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), new Formula.Relation(Call("asRat",
        Call("deltaSq", N("a"), N("b"), N("c"))), FormulaRelationOperator.Equal, Call("div", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat", Call("Natfactorial",
        Call("natDiv", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("b")))), FormulaBinaryOperator.Subtract, Parenthesized(N("c"))),
        D(2)))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", Call("natDiv", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add,
        Parenthesized(N("c")))), FormulaBinaryOperator.Subtract, Parenthesized(N("b"))), D(2))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", Call("natDiv", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add,
        Parenthesized(N("c")))), FormulaBinaryOperator.Subtract, Parenthesized(N("a"))), D(2)))))), Call("rat",
        Call("Natfactorial", new Formula.Binary(Parenthesized(Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b")))),
        FormulaBinaryOperator.Add, Parenthesized(N("c"))), D(2))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))))))));

    private static Formula F5() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("e", N("Nat"), All("f",
        N("Nat"), new Formula.Relation(Call("asNat", Call("lower", N("a"), N("b"), N("c"), N("d"), N("e"), N("f"))),
        FormulaRelationOperator.Equal, Call("max", Call("max", Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("b")))),
        FormulaBinaryOperator.Add, Parenthesized(N("c"))), D(2)), Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add, Parenthesized(N("e")))),
        FormulaBinaryOperator.Add, Parenthesized(N("f"))), D(2))), Call("max", Call("natDiv", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("d")), FormulaBinaryOperator.Add,
        Parenthesized(N("b")))), FormulaBinaryOperator.Add, Parenthesized(N("f"))), D(2)), Call("natDiv", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("d")), FormulaBinaryOperator.Add,
        Parenthesized(N("e")))), FormulaBinaryOperator.Add, Parenthesized(N("c"))), D(2))))))))))));

    private static Formula F6() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("e", N("Nat"), All("f",
        N("Nat"), new Formula.Relation(Call("asNat", Call("upper", N("a"), N("b"), N("c"), N("d"), N("e"), N("f"))),
        FormulaRelationOperator.Equal, Call("min", Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add,
        Parenthesized(N("b")))), FormulaBinaryOperator.Add, Parenthesized(N("d")))), FormulaBinaryOperator.Add,
        Parenthesized(N("e"))), D(2)), Call("min", Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add,
        Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(N("e")))), FormulaBinaryOperator.Add,
        Parenthesized(N("f"))), D(2)), Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("c")), FormulaBinaryOperator.Add,
        Parenthesized(N("a")))), FormulaBinaryOperator.Add, Parenthesized(N("f")))), FormulaBinaryOperator.Add,
        Parenthesized(N("d"))), D(2))))))))))));

    private static Formula F7() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("e", N("Nat"), All("f",
        N("Nat"), All("z", N("Nat"), new Formula.Relation(Call("asRat", Call("racahTerm", N("a"), N("b"), N("c"),
        N("d"), N("e"), N("f"), N("z"))), FormulaRelationOperator.Equal, Call("div", new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))),
        N("z"))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))), Call("asRat", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("rat",
        Call("Natfactorial", new Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("natDiv", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Add, Parenthesized(N("b")))), FormulaBinaryOperator.Add, Parenthesized(N("c"))),
        D(2))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Subtract, Parenthesized(Call("natDiv", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add,
        Parenthesized(N("e")))), FormulaBinaryOperator.Add, Parenthesized(N("f"))), D(2))))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Subtract, Parenthesized(Call("natDiv", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("d")), FormulaBinaryOperator.Add,
        Parenthesized(N("b")))), FormulaBinaryOperator.Add, Parenthesized(N("f"))), D(2))))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(N("z")), FormulaBinaryOperator.Subtract, Parenthesized(Call("natDiv", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("d")), FormulaBinaryOperator.Add,
        Parenthesized(N("e")))), FormulaBinaryOperator.Add, Parenthesized(N("c"))), D(2))))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Add,
        Parenthesized(N("b")))), FormulaBinaryOperator.Add, Parenthesized(N("d")))), FormulaBinaryOperator.Add,
        Parenthesized(N("e"))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(N("z")))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("b")), FormulaBinaryOperator.Add,
        Parenthesized(N("c")))), FormulaBinaryOperator.Add, Parenthesized(N("e")))), FormulaBinaryOperator.Add,
        Parenthesized(N("f"))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(N("z")))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(Call("natDiv", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("c")), FormulaBinaryOperator.Add,
        Parenthesized(N("a")))), FormulaBinaryOperator.Add, Parenthesized(N("f")))), FormulaBinaryOperator.Add,
        Parenthesized(N("d"))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(N("z"))))))))))))))))));

    private static Formula F8() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("e", N("Nat"), All("f",
        N("Nat"), new Formula.Relation(Call("asRat", Call("racahSum", N("a"), N("b"), N("c"), N("d"), N("e"),
        N("f"))), FormulaRelationOperator.Equal, Seq(Sum, Underscore, Grp(Seq(N("z"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(Call("upper", N("a"), N("b"), N("c"), N("d"), N("e"), N("f"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), Parenthesized(Call("ite", new
        Formula.Relation(Call("lower", N("a"), N("b"), N("c"), N("d"), N("e"), N("f")),
        FormulaRelationOperator.LessThanOrEqual, N("z")), Call("racahTerm", N("a"), N("b"), N("c"), N("d"), N("e"),
        N("f"), N("z")), D(0))))))))))));

    private static Formula F9() =>
        Disp(All("a", N("Nat"), All("b", N("Nat"), All("c", N("Nat"), All("d", N("Nat"), All("e", N("Nat"), All("f",
        N("Nat"), new Formula.Relation(Call("asReal", Call("sixJ", N("a"), N("b"), N("c"), N("d"), N("e"), N("f"))),
        FormulaRelationOperator.Equal, Call("ite", Call("admissible", N("a"), N("b"), N("c"), N("d"), N("e"), N("f")),
        new Formula.Binary(Parenthesized(Call("Realsqrt", Call("asReal", Call("real", Call("asRat", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("deltaSq",
        N("a"), N("b"), N("c"))), FormulaBinaryOperator.Multiply, Parenthesized(Call("deltaSq", N("a"), N("e"),
        N("f"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("deltaSq", N("d"), N("b"), N("f"))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("deltaSq", N("d"), N("e"), N("c"))))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real", Call("racahSum", N("a"), N("b"),
        N("c"), N("d"), N("e"), N("f")))))), D(0))))))))));

    private static Formula F10() =>
        Disp(All("k", N("Nat"), All("i", N("Nat"), new Formula.Relation(Call("asRat", Call("racahMonomial", N("k"),
        N("i"))), FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(N("k"),
        FormulaRelationOperator.LessThanOrEqual, N("i")), Call("div", Call("asRat", Call("rat", Call("Natfactorial",
        new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(N("k")))))), Call("rat",
        Call("Natfactorial", new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("k")))))), D(0))))));

    private static Formula F11() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), All("k", N("Nat"), new Formula.Relation(Call("asRat",
        Call("racahCoefficient", N("N"), N("j"), N("k"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))), N("k"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natchoose", N("j"), N("k")))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natchoose", new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(N("k"))), N("k")))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("div", new Formula.Binary(Parenthesized(Call("asRat",
        Call("rat", N("N")))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(N("k")))), FormulaBinaryOperator.Subtract, Parenthesized(D(1))))))), Call("rat",
        Call("Natfactorial", new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Add,
        Parenthesized(N("k")))))))))))));

    private static Formula F12() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), All("i", N("Nat"), new Formula.Relation(Call("asRat",
        Call("racahPolynomial", N("N"), N("j"), N("i"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Add, Parenthesized(Seq(Sum, Underscore,
        Grp(Seq(N("k"), InMacro, Call("range", N("j")))), Parenthesized(new
        Formula.Binary(Parenthesized(Call("racahCoefficient", N("N"), N("j"), new
        Formula.Binary(Parenthesized(N("k")), FormulaBinaryOperator.Add, Parenthesized(D(1))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("racahMonomial", new Formula.Binary(Parenthesized(N("k")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), N("i")))))))))))));

    private static Formula F13() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(D(2),
        FormulaRelationOperator.LessThanOrEqual, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThan, N("N"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro,
        Call("range", new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))))), Parenthesized(new Formula.Binary(Parenthesized(Call("div", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("asRat", Call("rat", Call("asNat", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))))), FormulaBinaryOperator.Add, Parenthesized(D(1))), new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", Call("asNat", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("rat", Call("asNat", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(D(1)),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("racahPolynomial", N("N"), N("j"), new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("harmonic", N("j"))))))))))));

    private static Formula F14() =>
        Disp(All("N", N("Nat"), All("i", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Call("asReal", Call("W", N("N"), N("i"), N("j"), N("l"))), FormulaRelationOperator.Equal,
        Call("sixJ", new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("i"))),
        new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("l"))), new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1))))))))));

    private static Formula F15() =>
        Disp(All("N", N("Nat"), All("i", N("Nat"), All("j", N("Nat"), new Formula.Relation(Call("asReal", Call("Wij",
        N("N"), N("i"), N("j"))), FormulaRelationOperator.Equal, Call("sixJ", new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("i"))), new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))))));

    private static Formula F16() =>
        Disp(All("i", N("Nat"), new Formula.Relation(Call("asReal", Call("casimir", N("i"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(Call("asReal", Call("real", N("i")))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("real", N("i"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))));

    private static Formula F17() =>
        Disp(All("k", N("Nat"), All("x", N("Rat"), new Formula.Relation(Call("asRat", Call("newtonBasis", N("k"),
        N("x"))), FormulaRelationOperator.Equal, Seq(Prod, Underscore, Grp(Seq(N("r"), InMacro, Call("range",
        N("k")))), Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("x")),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", N("r"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("x")),
        FormulaBinaryOperator.Add, Parenthesized(Call("rat", N("r"))))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))))))));

    private static Formula F19() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), All("f", new Formula.TypeArrow(N("Nat"), N("Rat")), All("g", new
        Formula.TypeArrow(N("Nat"), N("Rat")), new Formula.Logic(Parenthesized(new Formula.Relation(D(2),
        FormulaRelationOperator.LessThanOrEqual, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(N("f"), [D(0)]),
        FormulaRelationOperator.Equal, new Formula.Apply(N("g"), [D(0)]))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(All("i", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("i")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", Call("rat", N("N")))), D(2))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", new Formula.Power(Parenthesized(new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2)))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new Formula.Apply(N("f"),
        [N("i")])), FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Apply(N("f"), [new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1)))])))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("i")))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", Call("rat",
        N("N")))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", new
        Formula.Power(Parenthesized(N("i")), D(2)))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Apply(N("f"), [N("i")])), FormulaBinaryOperator.Subtract,
        Parenthesized(new Formula.Apply(N("f"), [new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))]))))))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("asRat", Call("rat", N("i")))))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("asRat", Call("rat", N("j")))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("rat", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Apply(N("f"), [N("i")])))))))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(All("i", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))),
        FormulaRelationOperator.LessThan, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("i")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", Call("rat", N("N")))), D(2))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", new Formula.Power(Parenthesized(new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1)))), D(2)))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new Formula.Apply(N("g"),
        [N("i")])), FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Apply(N("g"), [new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1)))])))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asRat", Call("rat", N("i")))), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", Call("rat",
        N("N")))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(Call("rat", new
        Formula.Power(Parenthesized(N("i")), D(2)))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Apply(N("g"), [N("i")])), FormulaBinaryOperator.Subtract,
        Parenthesized(new Formula.Apply(N("g"), [new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))]))))))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("asRat", Call("rat", N("i")))))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("asRat", Call("rat", N("j")))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("rat", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Apply(N("g"), [N("i")])))))))), FormulaLogicOperator.Implies, Parenthesized(All("i", N("Nat"), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("i"), FormulaRelationOperator.LessThan, N("N"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Apply(N("f"), [N("i")]),
        FormulaRelationOperator.Equal, new Formula.Apply(N("g"), [N("i")]))))))))))))))))));

    private static Formula F20() =>
        Disp(All("N", N("Rat"), All("i", N("Rat"), All("j", N("Rat"), All("k", N("Rat"), new
        Formula.Relation(Call("asRat", Call("certificatePolynomial", N("N"), N("i"), N("j"), N("k"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(N("N")), D(2))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j")))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), FormulaBinaryOperator.Subtract, Parenthesized(N("k")))),
        D(2))))), FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("i")))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(N("N")), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(N("j")))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1)))),
        FormulaBinaryOperator.Subtract, Parenthesized(N("k")))))))), FormulaBinaryOperator.Add, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Multiply,
        Parenthesized(new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(N("N")), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Power(Parenthesized(N("j")), D(2))))))))))))));

    private static Formula F21() =>
        Disp(All("N", N("Nat"), All("i", N("Nat"), All("j", N("Nat"), new Formula.Relation(Call("asRat",
        Call("normalizedRacah", N("N"), N("i"), N("j"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))), new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))), FormulaBinaryOperator.Add, Parenthesized(N("i")))),
        FormulaBinaryOperator.Add, Parenthesized(N("j"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("rat",
        N("N"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("deltaSq", new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("i"))), new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("deltaSq", new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("racahSum", new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("i"))), new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))), new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))), new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("j"))), new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))), new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))))))))));

    private static Formula F23() =>
        Disp(All("z", N("Int"), new Formula.Relation(Call("asRat", Call("invFactorial", N("z"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual,
        N("z")), Call("inv", Call("asRat", Call("rat", Call("Natfactorial", Call("toNat", N("z")))))), D(0)))));

    private static Formula F24() =>
        Disp(All("N", N("Nat"), All("i", N("Nat"), All("j", N("Nat"), All("k", N("Nat"), new
        Formula.Relation(Call("asRat", Call("factorialKernel", N("N"), N("i"), N("j"), N("k"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))), N("k"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Add, Parenthesized(N("i")))), FormulaBinaryOperator.Add, Parenthesized(N("j")))),
        FormulaBinaryOperator.Subtract, Parenthesized(N("k")))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(Call("asInt", Call("int",
        N("i")))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("k")))))), D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("j")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("int", N("k")))))), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("invFactorial", Call("asInt", Call("int", N("k"))))), D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt",
        Call("int", N("N")))), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))), FormulaBinaryOperator.Add,
        Parenthesized(Call("int", N("k"))))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("i"))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("j")))))))))))));

    private static Formula F25() =>
        Disp(All("N", N("Nat"), All("i", N("Nat"), All("j", N("Nat"), All("k", N("Nat"), new
        Formula.Relation(Call("asRat", Call("certificateBase", N("N"), N("i"), N("j"), N("k"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))), N("k"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("rat", Call("Natfactorial", new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Add, Parenthesized(N("i")))),
        FormulaBinaryOperator.Add, Parenthesized(N("j")))), FormulaBinaryOperator.Subtract, Parenthesized(N("k")))),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("i")))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("k")))))), D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("j")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("int", N("k")))))), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("invFactorial", Call("asInt", Call("int", N("k"))))), D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("N")))),
        FormulaBinaryOperator.Add, Parenthesized(Call("int", N("k"))))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("int", N("i"))))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int",
        N("j")))))))))))));

    private static Formula F26() =>
        Disp(All("N", N("Nat"), All("i", N("Nat"), All("j", N("Nat"), All("k", N("Nat"), new
        Formula.Relation(Call("asRat", Call("kernelFlux", N("N"), N("i"), N("j"), N("k"))),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asRat", new Formula.Negate(D(1)))),
        N("k"))), FormulaBinaryOperator.Multiply, Parenthesized(Call("certificatePolynomial", Call("rat", N("N")),
        Call("rat", N("i")), Call("rat", N("j")), Call("rat", N("k")))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("rat", Call("Natfactorial", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Add,
        Parenthesized(N("i")))), FormulaBinaryOperator.Add, Parenthesized(N("j")))), FormulaBinaryOperator.Subtract,
        Parenthesized(N("k")))))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("i")))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("k")))))), D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("invFactorial", new
        Formula.Binary(Parenthesized(Call("asInt", Call("int", N("j")))), FormulaBinaryOperator.Subtract,
        Parenthesized(Call("int", N("k")))))), D(2))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(Call("asInt", Call("int",
        N("k")))), FormulaBinaryOperator.Subtract, Parenthesized(D(1))))), D(2))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("invFactorial", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("asInt", Call("int", N("N")))),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))), FormulaBinaryOperator.Add, Parenthesized(Call("int",
        N("k"))))), FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("i"))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("int", N("j")))))))))))));

    private static Formula F27() =>
        Disp(All("N", N("Nat"), All("i", N("Nat"), All("j", N("Nat"), new Formula.Relation(Call("asRat",
        Call("racahPrefactor", N("N"), N("i"), N("j"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("rat", N("N"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("deltaSq", new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("i"))), new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))), new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("deltaSq", new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(N("j"))), new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))), new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))))))))));

    private static Formula F28() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), All("i", N("Nat"), new Formula.Relation(Call("asRat",
        Call("kernelSequence", N("N"), N("j"), N("i"))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(Call("racahPrefactor", N("N"), N("i"), N("j"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Seq(Sum, Underscore, Grp(Seq(N("k"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        Parenthesized(Call("factorialKernel", N("N"), N("i"), N("j"), N("k")))))))))));
}
