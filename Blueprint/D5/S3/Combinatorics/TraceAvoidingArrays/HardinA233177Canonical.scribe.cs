using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233177CanonicalDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.";
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-appearance representatives and exact complementary-pair colour fibres.",
        H("Canonical pair patterns on a finite linear order"),
        Blocks(
            Paragraph(Text("A canonical word introduces smaller labels before larger labels. "
                + "The cell order is an explicit parameter. The existence proof minimizes "
                + "the relabelling orbit in lexicographic order; exchanging an out-of-order "
                + "label with an absent smaller label would contradict minimality. "
                + "Induction on cells proves uniqueness from equality of label fibres.")),
            Node("Canonical", "Canonical words", CanonicalFormula(), false),
            Node("canonical_exists_unique", "A unique representative in each orbit",
                CanonicalUniqueFormula(), true),
            Node("Normal", "Individual-colour normalization", NormalFormula(), false),
            Node("FirstSides", "Fixed side at each first occurrence", FirstSidesFormula(), false),
            Node("normalization_iff", "Normalization is canonical form with fixed first sides",
                NormalizationFormula(), true),
            Node("Fibre", "Individual-colour lifts of a fixed pair pattern",
                FibreFormula(), false),
            Node("fibre_card", "Exact number of lifts", FibreCardFormula(), true),
            Node("canonical_pattern_card", "Six patterns per canonical representative",
                PatternCardFormula(), true),
            Node("normalized_card", "Weighted canonical-pattern count", NormalizedFormula(), true),
            Paragraph(Text("The complementary pairs are the fibres {0,5}, {1,4}, {2,3} "
                + "of D5.S3.Observer.Separation.BooleanRankThreeK4.beta. A private proved "
                + "equivalence sends a colour to its pair and the Boolean test 3 <= colour.val. "
                + "Fixing the smaller colour at the first occurrence leaves one independent "
                + "Boolean choice at every other cell. First occurrences are in bijection "
                + "with the used labels. A permutation of three labels is determined by "
                + "its values on two different labels. These statements concern finite "
                + "words and do not assert the four-row ladder recurrence.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, bool theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula CanonicalFormula()
    {
        var c = V("C"); var k = V("k"); var p = V("P");
        var body = All("i", c, All("b", Fin(k), Imp(Lt(V("b"), App(p, V("i"))),
            Ex("j", c, And(Lt(V("j"), V("i")), Eq(App(p, V("j")), V("b")))))));
        return All("C", Q("Type"), Instances([Call("LT", c)],
            All("k", Q("Nat"), All("P", Arrow(c, Fin(k)),
                Eq(Own("Canonical", p), Parenthesized(body))))));
    }

    private static Formula CanonicalUniqueFormula()
    {
        var c = V("C"); var k = V("k"); var p = V("P"); var q = V("Q");
        return FiniteOrder(All("k", Q("Nat"), All("P", Arrow(c, Fin(k)),
            Unique("Q", Arrow(c, Fin(k)), And(Own("Canonical", q),
                Ex("e", Call("Equiv.Perm", Fin(k)), Eq(q, Compose(V("e"), p))))))));
    }

    private static Formula NormalFormula()
    {
        var c = V("C"); var f = V("f"); var i = V("i");
        var x = App(f, i);
        Formula Before(int d) => Ex("j", c,
            And(Lt(V("j"), i), Eq(App(f, V("j")), Colour(d))));
        var body = All("i", c, And(
            Imp(Or(Eq(x, Colour(2)), Or(Eq(x, Colour(3)), Eq(x, Colour(4)))), Before(1)),
            Imp(Eq(x, Colour(3)), Before(2))));
        return Ordered(All("f", Arrow(c, Fin(D(6))),
            Eq(Own("Normal", f), Parenthesized(body))));
    }

    private static Formula FirstSidesFormula()
    {
        var c = V("C"); var f = V("f"); var i = V("i");
        var body = All("i", c, Imp(All("j", c, Imp(Lt(V("j"), i),
            Ne(Beta(App(f, V("j"))), Beta(App(f, i))))),
            Eq(Val(App(f, i)), Val(Beta(App(f, i))))));
        return Ordered(All("f", Arrow(c, Fin(D(6))),
            Eq(Own("FirstSides", f), Parenthesized(body))));
    }

    private static Formula NormalizationFormula()
    {
        var c = V("C"); var z = V("z"); var f = V("f");
        return FiniteOrder(All("z", c, Imp(All("i", c, Le(z, V("i"))),
            All("f", Arrow(c, Fin(D(6))), Imp(Eq(App(f, z), Colour(0)),
                Iff(Own("Normal", f), And(Own("Canonical", Compose(BetaFunction(), f)),
                    Own("FirstSides", f))))))));
    }

    private static Formula FibreFormula()
    {
        var c = V("C"); var p = V("P"); var f = V("f");
        return Ordered(All("P", Arrow(c, Fin(D(3))), Eq(Own("Fibre", p),
            Subtype("f", Arrow(c, Fin(D(6))), And(
                All("i", c, Eq(Beta(App(f, V("i"))), App(p, V("i")))),
                Own("FirstSides", f))))));
    }

    private static Formula FibreCardFormula()
    {
        var c = V("C"); var p = V("P");
        return FiniteOrder(All("P", Arrow(c, Fin(D(3))),
            Eq(Card(Own("Fibre", p)), Power(D(2), Sub(Call("Fintype.card", c),
                Card(Call("Set.range", p)))))));
    }

    private static Formula PatternCardFormula()
    {
        var c = V("C"); var s = V("S"); var p = V("P");
        var word = Arrow(c, Fin(D(3)));
        var invariant = All("e", Call("Equiv.Perm", Fin(D(3))), All("P", word,
            Iff(App(s, Compose(V("e"), p)), App(s, p))));
        var two = All("P", word, Imp(App(s, p), Ex("i", c, Ex("j", c,
            Ne(App(p, V("i")), App(p, V("j")))))));
        return FiniteOrder(All("S", Arrow(word, Q("Prop")), Imp(invariant, Imp(two,
            Eq(Card(Subtype("P", word, App(s, p))), Mul(D(6),
                Card(Subtype("P", word, And(App(s, p), Own("Canonical", p))))))))));
    }

    private static Formula NormalizedFormula()
    {
        var c = V("C"); var z = V("z"); var s = V("S");
        var f = V("f"); var p = V("P");
        var word = Arrow(c, Fin(D(3)));
        var patterns = Subtype("P", word, And(App(s, p), Own("Canonical", p)));
        var colours = Subtype("f", Arrow(c, Fin(D(6))), And(
            App(s, Compose(BetaFunction(), f)),
            And(Eq(App(f, z), Colour(0)), Own("Normal", f))));
        var summand = Power(D(2), Sub(Call("Fintype.card", c),
            Card(Call("Set.range", Call("Subtype.val", p)))));
        var sum = Call("Finset.sum", Typed(Q("Finset.univ"), Call("Finset", patterns)),
            Fn("P", patterns, summand));
        return FiniteOrder(All("z", c, Imp(All("i", c, Le(z, V("i"))),
            All("S", Arrow(word, Q("Prop")), Eq(Card(colours), sum)))));
    }

    private static Formula Ordered(Formula body) =>
        All("C", Q("Type"), Instances([Call("LT", V("C"))], body));
    private static Formula FiniteOrder(Formula body) =>
        All("C", Q("Type"), Instances(
            [Call("Fintype", V("C")), Call("LinearOrder", V("C"))], body));
    private static Formula Instances(Formula[] types, Formula body) =>
        Seq([.. types.SelectMany(t => new[] { OpenBracket, t, CloseBracket, Comma, Sp }), body]);
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Subtype(string name, Formula type, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, type, Sp, Slash, Slash, Sp,
            Parenthesized(body), CloseBrace);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Colour(int n) => Typed(Num(n), Fin(D(6)));
    private static Formula BetaFunction() =>
        Q("D5.S3.Observer.Separation.BooleanRankThreeK4.beta");
    private static Formula Beta(Formula x) => App(BetaFunction(), x);
    private static Formula Compose(Formula f, Formula g) => Call("Function.comp", f, g);
    private static Formula Card(Formula type) => Call("Nat.card", type);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Unique(string name, Formula type, Formula body) =>
        Seq(Exists, Bang, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
}
