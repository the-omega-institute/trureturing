using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class SumRulesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FluidDynamics/lichtenfelz2026zeitlin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J SumRules"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("claim", "claim", F0(),
                "Conjecture 1, page 6, section 2.2, equations (2.10)–(2.13): for every 1 ≤ j,l ≤ N−1, the four displayed identities hold; the inverse-Casimir identity alone requires j ≠ l. The complete source quotation, including the Casimir and harmonic-number conventions, is in the cited literature note. The encoding quantifies over natural N ≥ 2; W(N,i,j,l) is the top row i,j,l with bottom row (N−1)/2,(N−1)/2,(N−1)/2, and Wij(N,i,j) has top row i,(N−1)/2,(N−1)/2 and bottom row j,(N−1)/2,(N−1)/2. Each sixJ argument is twice the corresponding spin. The sum variable i+1 in range(N−1) traverses exactly 1,...,N−1. The first identity alone assumes j≠l. Harmonic numbers are rational and are cast to Real.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", F1(),
                "The four identities hold over their complete stated ranges. The Green inverse, parity addition, Jacobi diagonal and harmonic antidifference give the four conjuncts.", DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lichtenfelz-modin-preston-2026-zeitlin-sixj-identities"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("zeitlin-sumrules-" + name.Replace("_", "-").Replace(".", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(new Formula.Relation(Parenthesized(Seq(N("claim"), Colon, N("Prop"))), FormulaRelationOperator.Equal,
        All("N", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(D(2),
        FormulaRelationOperator.LessThanOrEqual, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("j"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("l"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("l"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.NotEqual, N("l"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))),
        Parenthesized(new Formula.Binary(Parenthesized(Call("div", new Formula.Binary(Parenthesized(new
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
        Parenthesized(D(1)))))))))))))))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("j"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("l"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("l"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Seq(Sum, Underscore,
        Grp(Seq(N("i"), InMacro, Call("range", new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))), Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asReal",
        new Formula.Negate(D(1)))), new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("casimir", new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real",
        Call("asNat", new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("W", N("N"), new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), N("j"), N("l"))), D(2)))))), FormulaRelationOperator.Equal,
        new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", new Formula.Negate(D(1)))), new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Add, Parenthesized(D(1))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("casimir", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(Call("casimir", N("l"))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("Wij", N("N"), N("l"), N("j")))))))))))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("j"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("l"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("l"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Seq(Sum, Underscore,
        Grp(Seq(N("i"), InMacro, Call("range", new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))), Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("casimir", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("asReal", Call("real", Call("asNat", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("W", N("N"), new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))), N("j"), N("l"))),
        D(2)))))), FormulaRelationOperator.Equal, Call("div", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asReal",
        Call("real", N("N")))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("casimir", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(Call("casimir", N("l"))))))), FormulaBinaryOperator.Subtract,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("casimir", N("j"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("casimir", N("l")))))), new Formula.Binary(Parenthesized(Call("asReal", Call("real",
        N("N")))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", Call("real", N("N")))), D(2))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))))))))))))), FormulaLogicOperator.And, Parenthesized(All("j", N("Nat"), new
        Formula.Logic(Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(D(1),
        FormulaRelationOperator.LessThanOrEqual, N("j"))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.LessThan, N("N"))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))),
        Parenthesized(new Formula.Binary(Parenthesized(Call("div", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real",
        Call("asNat", new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), Call("casimir", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", D(1), Call("asReal", Call("real", N("N"))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", new Formula.Negate(D(1)))), new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), FormulaBinaryOperator.Add, Parenthesized(N("j")))), FormulaBinaryOperator.Add,
        Parenthesized(N("N"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("Wij", N("N"), new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))), N("j")))))))))),
        FormulaRelationOperator.Equal, Call("div", new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real", Call("harmonic", N("j")))))),
        Call("real", N("N"))))))))))))))))));

    private static Formula F1() =>
        Disp(All("N", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(D(2),
        FormulaRelationOperator.LessThanOrEqual, N("N"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("j"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("l"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("l"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.NotEqual, N("l"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))),
        Parenthesized(new Formula.Binary(Parenthesized(Call("div", new Formula.Binary(Parenthesized(new
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
        Parenthesized(D(1)))))))))))))))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("j"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("l"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("l"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Seq(Sum, Underscore,
        Grp(Seq(N("i"), InMacro, Call("range", new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))), Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asReal",
        new Formula.Negate(D(1)))), new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(D(1))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("casimir", new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real",
        Call("asNat", new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("W", N("N"), new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), N("j"), N("l"))), D(2)))))), FormulaRelationOperator.Equal,
        new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", new Formula.Negate(D(1)))), new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Add, Parenthesized(D(1))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("casimir", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(Call("casimir", N("l"))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("Wij", N("N"), N("l"), N("j")))))))))))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Logic(Parenthesized(All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("j"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, N("l"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("l"), FormulaRelationOperator.LessThan,
        N("N"))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(Seq(Sum, Underscore,
        Grp(Seq(N("i"), InMacro, Call("range", new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))), Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("casimir", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("asReal", Call("real", Call("asNat", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1))))))))), FormulaBinaryOperator.Add, Parenthesized(D(1)))))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("W", N("N"), new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))), N("j"), N("l"))),
        D(2)))))), FormulaRelationOperator.Equal, Call("div", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(Call("asReal",
        Call("real", N("N")))), D(2))), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(Call("casimir", N("j"))),
        FormulaBinaryOperator.Add, Parenthesized(Call("casimir", N("l"))))))), FormulaBinaryOperator.Subtract,
        Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("casimir", N("j"))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("casimir", N("l")))))), new Formula.Binary(Parenthesized(Call("asReal", Call("real",
        N("N")))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", Call("real", N("N")))), D(2))), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1)))))))))))))), FormulaLogicOperator.And, Parenthesized(All("j", N("Nat"), new
        Formula.Logic(Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(D(1),
        FormulaRelationOperator.LessThanOrEqual, N("j"))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.LessThan, N("N"))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(Seq(Sum, Underscore, Grp(Seq(N("i"), InMacro, Call("range", new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))))),
        Parenthesized(new Formula.Binary(Parenthesized(Call("div", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real",
        Call("asNat", new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))),
        FormulaBinaryOperator.Add, Parenthesized(D(1))), Call("casimir", new Formula.Binary(Parenthesized(N("i")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", D(1), Call("asReal", Call("real", N("N"))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(Call("asReal", new Formula.Negate(D(1)))), new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), FormulaBinaryOperator.Add, Parenthesized(N("j")))), FormulaBinaryOperator.Add,
        Parenthesized(N("N"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("Wij", N("N"), new
        Formula.Binary(Parenthesized(N("i")), FormulaBinaryOperator.Add, Parenthesized(D(1))), N("j")))))))))),
        FormulaRelationOperator.Equal, Call("div", new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("asReal", Call("real", Call("harmonic", N("j")))))),
        Call("real", N("N")))))))))))))))));
}
