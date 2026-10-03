using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.ZeitlinSixJ;

internal sealed class OrthogonalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FluidDynamics/lichtenfelz2026zeitlin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Racah finite sums and the Zeitlin six-j identities.",
        H("Zeitlin Six-J Orthogonality"),
        Blocks(
            Paragraph(Text("Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.")),
            Node("physicalT", "physicalT", F0(),
                "The displayed equation is the defining expression of physicalT.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalH", "physicalH", F1(),
                "The displayed equation is the defining expression of physicalH.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalCasimir", "physicalCasimir", F2(),
                "The displayed equation is the defining expression of physicalCasimir.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalU_orthogonality", "physicalU orthogonality", F3(),
                "The physical Racah matrix is orthogonal. Its two recurrences, injective Casimir labels, nonzero Jacobi edges and stretched endpoint norm establish its Gram matrix.", DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)),
            Node("greenColumn", "greenColumn", F4(),
                "The displayed equation is the defining expression of greenColumn.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("greenMatrix", "greenMatrix", F5(),
                "The displayed equation is the defining expression of greenMatrix.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("jacobi_green_inverse", "jacobi green inverse", F6(),
                "The two one-sided pivot recurrences and boundary conditions construct the inverse of the finite Jacobi matrix. The product formula solves the homogeneous equation on each side and has unit diagonal residual.", DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("channelSpin", "channelSpin", F7(),
                "The displayed equation is the defining expression of channelSpin.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalA", "physicalA", F8(),
                "The displayed equation is the defining expression of physicalA.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalE", "physicalE", F9(),
                "The displayed equation is the defining expression of physicalE.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalLP", "physicalLP", F10(),
                "The displayed equation is the defining expression of physicalLP.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalRP", "physicalRP", F11(),
                "The displayed equation is the defining expression of physicalRP.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalG", "physicalG", F12(),
                "The displayed equation is the defining expression of physicalG.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("physicalSpectralInverse", "physicalSpectralInverse", F13(),
                "The displayed equation is the defining expression of physicalSpectralInverse.", DescribeRole.Definition, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("zeitlin-orthogonality-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F0() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalT", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, Call("finiteSixJJacobi", N("n"), N("n"),
        new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("l"))),
        Call("channelBase", N("n"), N("j"), N("l")), Call("channelWidth", N("n"), N("j"), N("l"))))))));

    private static Formula F1() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalH", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, Call("finiteSixJJacobi", N("n"), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("l"))), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), N("n"), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(N("l")), FormulaBinaryOperator.Subtract, Parenthesized(N("j"))))),
        Call("channelWidth", N("n"), N("j"), N("l"))))))));

    private static Formula F2() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), All("k", Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), new Formula.Relation(Call("asReal", Call("physicalCasimir", N("n"), N("j"), N("l"),
        N("k"))), FormulaRelationOperator.Equal, Call("asReal", Call("real", Call("asRat", new
        Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", Call("channelLabel", N("n"), N("j"),
        N("l"), Call("val", N("k"))))), D(2))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Binary(Parenthesized(Call("div", Call("asRat", Call("rat", Call("channelLabel", N("n"), N("j"),
        N("l"), Call("val", N("k"))))), D(2))), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))))))));

    private static Formula F3() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(N("l"),
        FormulaRelationOperator.LessThanOrEqual, N("n"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThanOrEqual, N("l"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("physicalU", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("transpose", Call("physicalU", N("n"), N("j"), N("l"))))), FormulaRelationOperator.Equal,
        D(1))))))))))));

    private static Formula F4() =>
        Disp(All("a", new Formula.TypeArrow(N("Nat"), N("Real")), All("e", new Formula.TypeArrow(N("Nat"), N("Real")),
        All("L", new Formula.TypeArrow(N("Nat"), N("Real")), All("R", new Formula.TypeArrow(N("Nat"), N("Real")),
        All("k", N("Nat"), All("h", N("Nat"), new Formula.Relation(Call("asReal", Call("greenColumn", N("a"), N("e"),
        N("L"), N("R"), N("k"), N("h"))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(Call("inv",
        new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Apply(N("L"), [N("h")])),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Apply(N("R"), [N("h")])))),
        FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Apply(N("a"), [N("h")]))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("ite", new Formula.Relation(N("k"),
        FormulaRelationOperator.LessThanOrEqual, N("h")), Seq(Prod, Underscore, Grp(Seq(N("t"), InMacro, Call("Ico",
        N("k"), N("h")))), Parenthesized(Call("div", new Formula.Negate(new Formula.Apply(N("e"), [N("t")])), new
        Formula.Apply(N("L"), [N("t")])))), Seq(Prod, Underscore, Grp(Seq(N("t"), InMacro, Call("Ico", N("h"),
        N("k")))), Parenthesized(Call("div", new Formula.Negate(new Formula.Apply(N("e"), [N("t")])), new
        Formula.Apply(N("R"), [new Formula.Binary(Parenthesized(N("t")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))])))))))))))))));

    private static Formula F5() =>
        Disp(All("m", N("Nat"), All("a", new Formula.TypeArrow(N("Nat"), N("Real")), All("e", new
        Formula.TypeArrow(N("Nat"), N("Real")), All("L", new Formula.TypeArrow(N("Nat"), N("Real")), All("R", new
        Formula.TypeArrow(N("Nat"), N("Real")), new Formula.Relation(Parenthesized(Seq(Call("greenMatrix", N("m"),
        N("a"), N("e"), N("L"), N("R")), Colon, Call("Matrix", Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new Formula.Binary(Parenthesized(N("m")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, Seq(N("k"),
        N("h"), Mapsto, Parenthesized(Call("greenColumn", N("a"), N("e"), N("L"), N("R"), Call("val", N("k")),
        Call("val", N("h"))))))))))));

    private static Formula F6() =>
        Disp(All("m", N("Nat"), All("a", new Formula.TypeArrow(N("Nat"), N("Real")), All("e", new
        Formula.TypeArrow(N("Nat"), N("Real")), All("L", new Formula.TypeArrow(N("Nat"), N("Real")), All("R", new
        Formula.TypeArrow(N("Nat"), N("Real")), new Formula.Logic(Parenthesized(All("k", N("Nat"), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("k"), FormulaRelationOperator.LessThanOrEqual, N("m"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Apply(N("L"), [N("k")]),
        FormulaRelationOperator.NotEqual, D(0)))))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Logic(Parenthesized(All("k", N("Nat"), new Formula.Logic(Parenthesized(new Formula.Relation(N("k"),
        FormulaRelationOperator.LessThanOrEqual, N("m"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Apply(N("R"), [N("k")]), FormulaRelationOperator.NotEqual, D(0)))))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(All("k", N("Nat"), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("k"), FormulaRelationOperator.LessThanOrEqual, N("m"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Apply(N("L"), [N("k")])), FormulaBinaryOperator.Add,
        Parenthesized(new Formula.Apply(N("R"), [N("k")])))), FormulaBinaryOperator.Subtract, Parenthesized(new
        Formula.Apply(N("a"), [N("k")]))), FormulaRelationOperator.NotEqual, D(0)))))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(N("a"), [D(0)]),
        FormulaRelationOperator.Equal, new Formula.Apply(N("L"), [D(0)]))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(new Formula.Apply(N("a"), [N("m")]),
        FormulaRelationOperator.Equal, new Formula.Apply(N("R"), [N("m")]))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(All("k", N("Nat"), new Formula.Logic(Parenthesized(new
        Formula.Relation(D(0), FormulaRelationOperator.LessThan, N("k"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Logic(Parenthesized(new Formula.Relation(N("k"),
        FormulaRelationOperator.LessThanOrEqual, N("m"))), FormulaLogicOperator.Implies, Parenthesized(new
        Formula.Relation(new Formula.Power(Parenthesized(new Formula.Apply(N("e"), [new
        Formula.Binary(Parenthesized(N("k")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))])), D(2)),
        FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new Formula.Apply(N("L"), [new
        Formula.Binary(Parenthesized(N("k")), FormulaBinaryOperator.Subtract, Parenthesized(D(1)))])),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new Formula.Apply(N("a"),
        [N("k")])), FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Apply(N("L"), [N("k")])))))))))))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(Parenthesized(All("k", N("Nat"), new
        Formula.Logic(Parenthesized(new Formula.Relation(N("k"), FormulaRelationOperator.LessThan, N("m"))),
        FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new Formula.Power(Parenthesized(new
        Formula.Apply(N("e"), [N("k")])), D(2)), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Apply(N("R"), [new Formula.Binary(Parenthesized(N("k")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))])), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Apply(N("a"), [N("k")])), FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Apply(N("R"),
        [N("k")])))))))))), FormulaLogicOperator.Implies, Parenthesized(new Formula.Relation(new
        Formula.Binary(Parenthesized(Call("jacobiMatrix", N("m"), Seq(N("k"), Mapsto, Parenthesized(new
        Formula.Apply(N("a"), [Call("val", N("k"))]))), Seq(N("k"), Mapsto, Parenthesized(new Formula.Apply(N("e"),
        [Call("val", N("k"))]))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("greenMatrix", N("m"), N("a"),
        N("e"), N("L"), N("R")))), FormulaRelationOperator.Equal, D(1))))))))))))))))))))));

    private static Formula F7() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), All("t", N("Nat"), new
        Formula.Relation(Call("asRat", Call("channelSpin", N("n"), N("j"), N("l"), N("t"))),
        FormulaRelationOperator.Equal, Call("div", Call("asRat", Call("rat", Call("channelLabel", N("n"), N("j"),
        N("l"), N("t")))), D(2))))))));

    private static Formula F8() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), All("t", N("Nat"), new
        Formula.Relation(Call("asReal", Call("physicalA", N("n"), N("j"), N("l"), N("t"))),
        FormulaRelationOperator.Equal, Call("asReal", Call("real", Call("recurrenceDiagonalQ", N("n"), N("n"), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new
        Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(N("l"))),
        Call("channelLabel", N("n"), N("j"), N("l"), N("t")))))))))));

    private static Formula F9() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), All("t", N("Nat"), new
        Formula.Relation(Call("asReal", Call("physicalE", N("n"), N("j"), N("l"), N("t"))),
        FormulaRelationOperator.Equal, Call("normalizedUpper", N("n"), N("n"), new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("j"))), new Formula.Binary(Parenthesized(D(2)),
        FormulaBinaryOperator.Multiply, Parenthesized(N("l"))), Call("channelLabel", N("n"), N("j"), N("l"),
        N("t")))))))));

    private static Formula F10() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), All("t", N("Nat"), new
        Formula.Relation(Call("asReal", Call("physicalLP", N("n"), N("j"), N("l"), N("t"))),
        FormulaRelationOperator.Equal, Call("asReal", Call("real", Call("pivotLeft", Call("div", Call("asRat",
        Call("rat", N("n"))), D(2)), Call("rat", N("j")), Call("rat", N("l")), Call("channelSpin", N("n"), N("j"),
        N("l"), N("t")))))))))));

    private static Formula F11() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), All("t", N("Nat"), new
        Formula.Relation(Call("asReal", Call("physicalRP", N("n"), N("j"), N("l"), N("t"))),
        FormulaRelationOperator.Equal, Call("asReal", Call("real", Call("pivotRight", Call("div", Call("asRat",
        Call("rat", N("n"))), D(2)), Call("rat", N("j")), Call("rat", N("l")), Call("channelSpin", N("n"), N("j"),
        N("l"), N("t")))))))))));

    private static Formula F12() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalG", N("n"), N("j"), N("l")), Colon, Call("Matrix",
        Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, Call("greenMatrix", Call("channelWidth",
        N("n"), N("j"), N("l")), Call("physicalA", N("n"), N("j"), N("l")), Call("physicalE", N("n"), N("j"), N("l")),
        Call("physicalLP", N("n"), N("j"), N("l")), Call("physicalRP", N("n"), N("j"), N("l"))))))));

    private static Formula F13() =>
        Disp(All("n", N("Nat"), All("j", N("Nat"), All("l", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("physicalSpectralInverse", N("n"), N("j"), N("l")), Colon,
        Call("Matrix", Call("Fin", new Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))), Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), N("Real")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("physicalU", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("diagonal", Seq(N("i"), Colon, Call("Fin", new
        Formula.Binary(Parenthesized(Call("channelWidth", N("n"), N("j"), N("l"))), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))), Mapsto, Parenthesized(Call("inv", Call("casimir", new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(N("l")), FormulaBinaryOperator.Subtract, Parenthesized(N("j")))),
        FormulaBinaryOperator.Add, Parenthesized(Call("val", N("i")))))))))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("transpose", Call("physicalU", N("n"), N("j"), N("l"))))))))));
}
