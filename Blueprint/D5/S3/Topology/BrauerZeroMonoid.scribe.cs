using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class BrauerZeroMonoidDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/BrauerZeroMonoid.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Loop-zero matching monoid", H("Loop-zero matching monoid"), Blocks(
            Paragraph(Text("Option.none is an absorbing zero. Option.some d retains the " +
                "literal boundary matching d. The product follows the sewn " +
                "paths when there is no internal loop, and is zero when a loop " +
                "occurs. These definitions include zero strands.")),

            Node("ZeroMatching", All("N", Nat(), Eq(Call("ZeroMatching", X("N")),
                Call("Option", Call("Matching", Call("Boundary", X("N")))))),
                "The carrier adjoins a single zero to the set of matchings."),
            Node("zeroMatchingMonoid", All("N", Nat(), And(
                Eq(Call("MonoidWithZero.toMulZeroOneClass", Call("zeroMatchingMonoid", X("N"))),
                    Record(Field("mul", N("multiply")),
                        Field("one", Call("Option.some", Call("identityMatching", X("N")))),
                Field("zero", N("Option.none")), Field("zero_mul", N("multiply_none_left")),
                        Field("mul_zero", N("multiply_none_right")))),
                All("a", Call("ZeroMatching", X("N")), All("b", Call("ZeroMatching", X("N")),
                    Eq(Call("multiply", X("a"), X("b")),
                        Call("Option.casesOn", X("a"), N("Option.none"),
                            Fn("d", Matchings(), Call("Option.casesOn", X("b"), N("Option.none"),
                                Fn("e", Matchings(), Product()))))))))),
                "The record displays the defining operations and zero laws. Its" +
                " associativity field is multiply_assoc; the unit laws use " +
                "composite_left_identity, composite_right_identity and the " +
                "corresponding zero loop counts. Option.casesOn expands the " +
                "literal private multiply pattern match."),
            Node("some_mul_some", All("N", Nat(), All("d", Matchings(), All("e", Matchings(),
                Eq(Mul(Typed(Call("Option.some", X("d")), Call("ZeroMatching", X("N"))),
                    Call("Option.some", X("e"))), Product())))),
                "This is the multiplication of zeroMatchingMonoid.", DescribeRole.Theorem))));

    private static Formula Matchings() => Call("Matching", Call("Boundary", X("N")));
    private static Formula Product() => If(Eq(Call("internalLoopCount", X("d"), X("e")), D(0)),
        Call("Option.some", Call("composite", X("d"), X("e"))), N("Option.none"));


    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/poncini2023planar");
    private static Formula X(string name) => F.Id(name);
    private static Formula N(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((s, i) =>
        i == 0 ? new[] { N(s) } : new[] { Dot, N(s) }).ToArray());
    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula D(long n) => n < 0 ? Negate(D(-n)) : Num(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) => Typed(X(name), type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Bound(name, type), Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) =>
        new Formula.Power(Parenthesized(a), Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula If(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Dite(string name, Formula c, Formula a, Formula b) =>
        Call("dite", c, Fn(name, c, a), Call("Function.const", Call("Not", c), b));
    private static Formula Nat() => N("Nat");
    private static Formula IntType() => N("Int");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula SubVal(Formula x) => Call("Subtype.val", x);
    private static Formula OmegaProof() => Seq(N("by"), Sp, N("omega"));
    private static Formula FinMk(Formula x, Formula proof) => Call("Fin.mk", x, proof);
    private static Formula Embed(Formula x) => FinMk(Val(x), OmegaProof());
    private static Formula Pair(Formula a, Formula b) => Call("Prod.mk", a, b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Call("Finset.sum", Call("Finset.univ"), Fn(name, type, body));
    private static Formula Smul(Formula a, Formula b) => Call("HSMul.hSMul", a, b);
    private static Formula Ring(Formula body) => All("R", N("Type"),
        Seq(OpenBracket, Call("CommRing", X("R")), CloseBracket, Sp, body));
    private static Formula Group(Formula body) => All("A", N("Type"),
        Seq(OpenBracket, Call("AddCommGroup", X("A")), CloseBracket, Sp, body));
    private static Formula Vector() => Arrow(Fin(D(8192)), IntType());
    private static Formula ZeroVector() => Call("Function.const", Fin(D(8192)), D(0));
    private static Formula Field(string name, Formula value) =>
        Seq(Q(name), Sp, Colon, F.Eq, Sp, value);
    private static Formula Record(params Formula[] fields) => Seq(OpenBrace, Sp,
        Seq(fields.SelectMany((f, i) => i == 0 ? new[] { f } :
            new[] { Comma, Sp, f }).ToArray()), Sp, CloseBrace);
    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, bool literature = false,
        bool acknowledgeSource = false) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) :
                acknowledgeSource ? AssessedProvenance.FromRepo(Source) :
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

}
