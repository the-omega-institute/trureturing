using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class WeakShuffleNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/WeakShuffleNormalization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mammez2022weakshuffle");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mammez's weak shuffle normalization conjecture holds for every alphabet.",
        H("Normalization of weak shuffle products"),
        Blocks(
            Paragraph(Text(
                "Mammez, Weak stuffle algebras, Proposition 3.9 and Conjecture 3.10, "
                + "defines a weak shuffle product by the displayed two-branch recursion. "
                + "The source says: “Proposition [3.9] is still true for any countable "
                + "alphabet.” The theorem below proves the same normalization for every "
                + "alphabet; the word carrier is a finitely supported function on lists.")),
            Describe.Lean(
                DescribeId.Create("word-coefficient-carrier"),
                DeclarationHandle.Create(Prefix + "KX"),
                H("Finitely supported word coefficients"),
                StatementSource.FromAuthor(Disp(KXFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "KX X K is the finitely supported K-valued function on List X, with "
                    + "the implicit Zero K instance used by the Finsupp carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weak-shuffle-word-recursion"),
                DeclarationHandle.Create(Prefix + "wsWord"),
                H("Weak shuffle recursion on words"),
                StatementSource.FromAuthor(Disp(WsWordFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The empty-word branches are singleton coefficients. For nonempty words "
                    + "the first coefficient prefixes the left head and recurses on the left "
                    + "tail, while the second coefficient prefixes the right head and recurses "
                    + "on the right tail."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weak-shuffle-bilinear-extension"),
                DeclarationHandle.Create(Prefix + "wsMul"),
                H("Bilinear extension of the word product"),
                StatementSource.FromAuthor(Disp(WsMulFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "wsMul sums the recursive word product over the finite supports of its "
                    + "two Finsupp arguments and multiplies the two coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weak-shuffle-condition"),
                DeclarationHandle.Create(Prefix + "IsWeakShuffle"),
                H("Associative and commutative weak shuffle products"),
                StatementSource.FromAuthor(Disp(IsWeakShuffleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "IsWeakShuffle requires commutativity and associativity of wsMul for all "
                    + "Finsupp inputs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-first-coefficient"),
                DeclarationHandle.Create(Prefix + "norm1"),
                H("First normalized coefficient"),
                StatementSource.FromAuthor(Disp(Norm1Formula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The source's first normalization bullet assigns one to an exceptional "
                    + "ordered pair, zero to its reverse exceptional pair, and otherwise "
                    + "keeps the original coefficient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-second-coefficient"),
                DeclarationHandle.Create(Prefix + "norm2"),
                H("Second normalized coefficient"),
                StatementSource.FromAuthor(Disp(Norm2Formula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "On the diagonal norm2 keeps f2; off the diagonal it uses the reversed "
                    + "first normalized coefficient, exactly as in the source's bullets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mammez-conjecture-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Mammez Conjecture 3.10"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Verbatim source statement (Conjecture 3.10, printed p. 18): "
                    + "“Proposition [3.9] is still true for any countable alphabet.” "
                    + "The Lean claim quantifies over every alphabet X and expresses the "
                    + "algebra isomorphism as a linear equivalence fixing the empty word."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mammez-conjecture-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Normalization for every alphabet"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The diagonal word rescaling has finite-support exponents. Associativity "
                    + "forces barriers for every exceptional pair, and the path exponent "
                    + "identity makes the rescaling intertwine the two products. Thus the "
                    + "source conjecture holds for every alphabet, including uncountable ones."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mammez-2022-weak-shuffle-normalization"),
                    ResolutionKind.Proved)))));

    private static Formula KXFormula() =>
        All("X", F.Id("Type"), All("K", F.Id("Type"),
            Seq(OpenBracket, Call("Zero", F.Id("K")), CloseBracket, Sp,
                Eq(Call("KX", F.Id("X"), F.Id("K")),
                    Call("Finsupp", Call("List", F.Id("X")), F.Id("K"))))));

    private static Formula WsWordFormula()
    {
        var f1 = F.Id("f1"); var f2 = F.Id("f2");
        var u = F.Id("u"); var v = F.Id("v");
        var a = F.Id("a"); var b = F.Id("b");
        var left = Mul(Call("f1", a, b),
            QCall("Finsupp.mapDomain", QCall("List.cons", a),
                Call("wsWord", f1, f2, u, Cons(b, v))));
        var right = Mul(Call("f2", a, b),
            QCall("Finsupp.mapDomain", QCall("List.cons", b),
                Call("wsWord", f1, f2, Cons(a, u), v)));
        var cases = Seq(
            Keyword("match"), Sp, Seq(u, Comma, Sp, v), Sp, Keyword("with"), Sp,
            new Formula.Aligned([
                Seq(Bar, Sp, Seq(OpenBracket, CloseBracket), Comma, Sp, v,
                    Sp, Mapsto, Sp, QCall("Finsupp.single", v, D(1))),
                Seq(Bar, Sp, u, Comma, Sp, Seq(OpenBracket, CloseBracket),
                    Sp, Mapsto, Sp, QCall("Finsupp.single", u, D(1))),
                Seq(Bar, Sp, Cons(a, u), Comma, Sp, Cons(b, v), Sp,
                    Mapsto, Sp, Add(left, right))]));
        return Forall("X", F.Id("Type"), Forall("K", F.Id("Type"),
            Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp,
            Forall("f1", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
                Forall("f2", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
                    Forall("u", Call("List", F.Id("X")),
                    Forall("v", Call("List", F.Id("X")),
                        Eq(Call("wsWord", f1, f2, u, v), cases))))))));
    }

    private static Formula WsMulFormula() =>
        Forall("X", F.Id("Type"), Forall("K", F.Id("Type"),
            Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp,
            Forall("f1", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
            Forall("f2", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
                Forall("x", Call("KX", F.Id("X"), F.Id("K")),
                    Forall("y", Call("KX", F.Id("X"), F.Id("K")),
                        Eq(Call("wsMul", F.Id("f1"), F.Id("f2"), F.Id("x"), F.Id("y")),
                            QCall("Finsupp.sum", F.Id("x"),
                                Fun("u", Call("List", F.Id("X")),
                                    Fun("a", F.Id("K"),
                                        QCall("Finsupp.sum", F.Id("y"),
                                            Fun("v", Call("List", F.Id("X")),
                                                Fun("b", F.Id("K"),
                                                    Mul(Mul(F.Id("a"), F.Id("b")),
                                                        Call("wsWord", F.Id("f1"), F.Id("f2"), F.Id("u"), F.Id("v")))))))))))))))));

    private static Formula IsWeakShuffleFormula() =>
        Forall("X", F.Id("Type"), Forall("K", F.Id("Type"),
            Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp,
            Forall("f1", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
            Forall("f2", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
                new Formula.Logic(Call("IsWeakShuffle", F.Id("f1"), F.Id("f2")), FormulaLogicOperator.Iff, Parenthesized(And(
                    Forall("x", Call("KX", F.Id("X"), F.Id("K")),
                        Forall("y", Call("KX", F.Id("X"), F.Id("K")),
                            Eq(Call("wsMul", F.Id("f1"), F.Id("f2"), F.Id("x"), F.Id("y")),
                                Call("wsMul", F.Id("f1"), F.Id("f2"), F.Id("y"), F.Id("x"))))),
                    Forall("x", Call("KX", F.Id("X"), F.Id("K")),
                        Forall("y", Call("KX", F.Id("X"), F.Id("K")),
                            Forall("z", Call("KX", F.Id("X"), F.Id("K")),
                                Eq(Call("wsMul", F.Id("f1"), F.Id("f2"),
                                        Call("wsMul", F.Id("f1"), F.Id("f2"), F.Id("x"), F.Id("y")), F.Id("z")),
                                    Call("wsMul", F.Id("f1"), F.Id("f2"), F.Id("x"),
                                        Call("wsMul", F.Id("f1"), F.Id("f2"), F.Id("y"), F.Id("z")))))))))))))));

    private static Formula Norm1Formula() =>
        Forall("X", F.Id("Type"), Forall("K", F.Id("Type"),
            Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp,
                Seq(OpenBracket, Call("DecidableEq", F.Id("X")), CloseBracket, Sp,
            Forall("f1", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
            Forall("a", F.Id("X"), Forall("b", F.Id("X"),
                Eq(Call("norm1", F.Id("f1"), F.Id("a"), F.Id("b")),
                    If(And(Ne(F.Id("a"), F.Id("b")),
                            Not(Member(Call("f1", F.Id("a"), F.Id("b")), Set01()))),
                        D(1), If(And(Ne(F.Id("a"), F.Id("b")),
                            Not(Member(Call("f1", F.Id("b"), F.Id("a")), Set01()))),
                            D(0), Call("f1", F.Id("a"), F.Id("b"))))))))))));

    private static Formula Norm2Formula() =>
        Forall("X", F.Id("Type"), Forall("K", F.Id("Type"),
            Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp,
                Seq(OpenBracket, Call("DecidableEq", F.Id("X")), CloseBracket, Sp,
            Forall("f1", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
            Forall("f2", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
                Forall("a", F.Id("X"), Forall("b", F.Id("X"),
                    Eq(Call("norm2", F.Id("f1"), F.Id("f2"), F.Id("a"), F.Id("b")),
                        If(Eq(F.Id("a"), F.Id("b")), Call("f2", F.Id("a"), F.Id("a")),
                            Call("norm1", F.Id("f1"), F.Id("b"), F.Id("a"))))))))))));

    private static Formula ClaimFormula() =>
        Forall("K", F.Id("Type"),
            Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp,
                Seq(OpenBracket, Call("CharZero", F.Id("K")), CloseBracket, Sp,
            Forall("X", F.Id("Type"),
                Seq(OpenBracket, Call("DecidableEq", F.Id("X")), CloseBracket, Sp,
            Forall("f1", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
                Forall("f2", Arrow(F.Id("X"), Arrow(F.Id("X"), F.Id("K"))),
                    Imp(Call("IsWeakShuffle", F.Id("f1"), F.Id("f2")),
                        Exists("Phi", Call("LinearEquiv", F.Id("K"), Call("KX", F.Id("X"), F.Id("K")),
                            Call("KX", F.Id("X"), F.Id("K"))),
                            And(Eq(Call("Phi", QCall("Finsupp.single", Seq(OpenBracket, CloseBracket), D(1))),
                                    QCall("Finsupp.single", Seq(OpenBracket, CloseBracket), D(1))),
                                Forall("x", Call("KX", F.Id("X"), F.Id("K")),
                                    Forall("y", Call("KX", F.Id("X"), F.Id("K")),
                                        Eq(Call("Phi", Call("wsMul", F.Id("f1"), F.Id("f2"), F.Id("x"), F.Id("y"))),
                                            Call("wsMul", Call("norm1", F.Id("f1")), Call("norm2", F.Id("f1"), F.Id("f2")),
                                                Call("Phi", F.Id("x")), Call("Phi", F.Id("y"))))))))))))))));

    private static Formula ResultFormula() => F.Id("claim");
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula All(string name, Formula type, Formula body) => Forall(name, type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula QCall(string name, params Formula[] args)
    {
        var parts = name.Split('.');
        Formula qualified = Seq(Operatorname, Grp(F.Id(parts[0]), Dot, F.Id(parts[1])));
        return new Formula.Apply(qualified, [.. args]);
    }
    private static Formula Keyword(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Cons(Formula head, Formula tail) => QCall("List.cons", head, tail);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Keyword("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Set01() => Seq(OpenBrace, D(0), Comma, Sp, D(1), CloseBrace);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Keyword("if"), Sp, Parenthesized(condition), Sp, Keyword("then"), Sp, yes, Sp, Keyword("else"), Sp, no);
}
