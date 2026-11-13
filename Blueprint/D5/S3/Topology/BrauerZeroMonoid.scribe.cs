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
                And(Eq(Typed(D(1), Call("ZeroMatching", X("N"))),
                    Call("Option.some", Call("identityMatching", X("N")))),
                    Eq(Typed(D(0), Call("ZeroMatching", X("N"))), N("Option.none"))),
                All("a", Call("ZeroMatching", X("N")), All("b", Call("ZeroMatching", X("N")), And(
                    Eq(Mul(X("a"), X("b")), Call("multiply", X("a"), X("b"))),
                    Eq(Call("multiply", X("a"), X("b")),
                        Call("Option.casesOn", X("a"), N("Option.none"),
                            Fn("d", Matchings(), Call("Option.casesOn", X("b"), N("Option.none"),
                                Fn("e", Matchings(), Product())))))))))),
                "These are the literal one, zero and mul fields of zeroMatchingMonoid. Its " +
                "associativity field is multiply_assoc; the unit laws use " +
                "composite_left_identity, composite_right_identity and the " +
                "corresponding zero loop counts. Option.casesOn expands the " +
                "literal private multiply pattern match. The zero_mul and mul_zero fields " +
                "are multiply_none_left and multiply_none_right."),
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

    private static Formula N(string name) => Q(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((s, i) =>
        i == 0 ? new[] { NamePart(s) } : new[] { Dot, NamePart(s) }).ToArray());
    private static Formula NamePart(string name)
    {
        bool prime = name.EndsWith('\'');
        var words = name.Replace("'", "").Split('_');
        Formula result = F.Id(words[^1]);
        for (int i = words.Length - 2; i >= 0; --i)
            result = Seq(F.Id(words[i]), Underscore, Grp(result));
        return prime ? Seq(Operatorname, Grp(result), Apos) : Seq(Operatorname, Grp(result));
    }

    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula D(long n) => n < 0 ? Negate(D(-n)) : Num(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) => Typed(X(name), type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Bound(name, type), Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula If(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Nat() => N("Nat");
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
