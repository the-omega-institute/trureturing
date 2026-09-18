using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ChauveZhangUnaryNeighborhoodRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/chauve2025neighborhoods");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary words refute unary minimality for condensed and super condensed neighborhoods.",
        H("Unary Neighborhood Minimality Refuted"),
        Blocks(
            Node(
                "levenshtein-recurrence",
                "Levenshtein distance",
                "levenshtein",
                LevenshteinFormula(),
                "The executable distance uses the Wagner--Fischer recurrence with insertion, "
                    + "deletion, and substitution cost one. ASSUMED-UNVERIFIED: no edit-script "
                    + "datatype or proof that this recurrence equals the minimum edit-script "
                    + "cost is formalized here.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "levenshtein-neighborhood",
                "The Levenshtein neighborhood",
                "neighborhood",
                NeighborhoodFormula(),
                "Equation (2.1) is represented literally as the set of words whose distance "
                    + "from w is at most d.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "condensed-neighborhood",
                "The condensed neighborhood",
                "condensed",
                CondensedFormula(),
                "Equation (2.2) retains exactly the neighborhood words with no distinct prefix "
                    + "in the same neighborhood. IsPrefix(y,x) is Lean's y <+: x relation.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "super-condensed-neighborhood",
                "The super condensed neighborhood",
                "superCondensed",
                SuperCondensedFormula(),
                "Equation (2.3) retains exactly the neighborhood words with no distinct "
                    + "contiguous subword in the same neighborhood. IsInfix(y,x) is Lean's "
                    + "y <:+: x relation.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "condensed-unary-minimality-claim",
                "Condensed unary minimality",
                "claimCondensed",
                ClaimCondensedFormula(),
                ClaimSourceText("condensed"),
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "condensed-unary-minimality-refuted",
                "The condensed claim fails at n = 3 and d = 2",
                "resultCondensed",
                ResultCondensedFormula(),
                "Over the binary alphabet, CN(000,2) is {0, 10, 110}, while CN(001,2) "
                    + "is {0, 1}. Their cardinalities are three and two, so 000 does not "
                    + "minimize the condensed neighborhood.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "chauve-zhang-condensed-neighborhood-unary-minimality"),
                    ResolutionKind.Refuted)),
            Node(
                "super-condensed-unary-minimality-claim",
                "Super condensed unary minimality",
                "claimSuperCondensed",
                ClaimSuperCondensedFormula(),
                ClaimSourceText("super condensed"),
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "super-condensed-unary-minimality-refuted",
                "The super condensed claim fails at n = 4 and d = 1",
                "resultSuperCondensed",
                ResultSuperCondensedFormula(),
                "Over the binary alphabet, SCN(0000,1) is {000, 0010, 0100}, while "
                    + "SCN(0011,1) is {001, 011}. Their cardinalities are three and two, "
                    + "so 0000 does not minimize the super condensed neighborhood.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "chauve-zhang-super-condensed-neighborhood-unary-minimality"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static string ClaimSourceText(string subject) =>
        "The closing question reads: \"It is thus natural to ask if a similar property holds "
            + "for condensed and super condensed neighborhoods, namely that unary words have "
            + "the smallest condensed or super condensed neighborhoods.\" The definitions read: "
            + "\"N(w, d) = {x ∈ Σ* | d_lev(x, w) ≤ d}\" (2.1); "
            + "\"CN(w, d) = N(w, d) \\ N(w, d)Σ⁺\" (2.2); and "
            + "\"SCN(w, d) = N(w, d) \\ (Σ*N(w, d)Σ⁺ ∪ Σ⁺N(w, d)Σ*)\" "
            + "(2.3). The displayed proposition is the " + subject
            + " half of that question, with no restriction on d.";

    private static Formula LevenshteinFormula()
    {
        var alpha = Alpha;
        var x = F.Id("x");
        var y = F.Id("y");
        var xs = F.Id("xs");
        var ys = F.Id("ys");
        var empty = Seq(OpenBracket, CloseBracket);
        var baseLeft = Equal(Call("levenshtein", empty, ys), Length(ys));
        var baseRight = Equal(Call("levenshtein", xs, empty), Length(xs));
        var delete = Add(Call("levenshtein", xs, Cons(y, ys)), D(1));
        var insert = Add(Call("levenshtein", Cons(x, xs), ys), D(1));
        var align = Add(
            Call("levenshtein", xs, ys),
            Call("ite", Equal(x, y), D(0), D(1)));
        var recurrence = Equal(
            Call("levenshtein", Cons(x, xs), Cons(y, ys)),
            Call("min", delete, Call("min", insert, align)));
        var clauses = Conjoin(
            ForAll("ys", ListOf(alpha), baseLeft),
            ForAll("xs", ListOf(alpha), baseRight),
            ForAll("x", alpha,
                ForAll("y", alpha,
                    ForAll("xs", ListOf(alpha),
                        ForAll("ys", ListOf(alpha), recurrence)))));
        return Disp(WithAlphabet(clauses, finite: false));
    }

    private static Formula NeighborhoodFormula()
    {
        var alpha = Alpha;
        var w = F.Id("w");
        var d = F.Id("d");
        var x = F.Id("x");
        var set = SetOf(x, ListOf(alpha),
            LessOrEqual(Call("levenshtein", x, w), d));
        var equation = Equal(Call("neighborhood", w, d), set);
        return Disp(WithAlphabet(
            ForAll("w", ListOf(alpha), ForAll("d", Naturals(), equation)),
            finite: false));
    }

    private static Formula CondensedFormula()
    {
        var alpha = Alpha;
        var w = F.Id("w");
        var d = F.Id("d");
        var x = F.Id("x");
        var y = F.Id("y");
        var neighborhood = Call("neighborhood", w, d);
        var noProperPrefix = ForAll("y", ListOf(alpha),
            Implies(
                Call("IsPrefix", y, x),
                Implies(
                    NotEqual(y, x),
                    new Formula.Not(Member(y, neighborhood)))));
        var set = SetOf(x, ListOf(alpha), And(Member(x, neighborhood), noProperPrefix));
        var equation = Equal(Call("condensed", w, d), set);
        return Disp(WithAlphabet(
            ForAll("w", ListOf(alpha), ForAll("d", Naturals(), equation)),
            finite: false));
    }

    private static Formula SuperCondensedFormula()
    {
        var alpha = Alpha;
        var w = F.Id("w");
        var d = F.Id("d");
        var x = F.Id("x");
        var y = F.Id("y");
        var neighborhood = Call("neighborhood", w, d);
        var noProperSubword = ForAll("y", ListOf(alpha),
            Implies(
                Call("IsInfix", y, x),
                Implies(
                    NotEqual(y, x),
                    new Formula.Not(Member(y, neighborhood)))));
        var set = SetOf(x, ListOf(alpha), And(Member(x, neighborhood), noProperSubword));
        var equation = Equal(Call("superCondensed", w, d), set);
        return Disp(WithAlphabet(
            ForAll("w", ListOf(alpha), ForAll("d", Naturals(), equation)),
            finite: false));
    }

    private static Formula ClaimCondensedFormula() => ClaimFormula(
        "claimCondensed", "condensed");

    private static Formula ClaimSuperCondensedFormula() => ClaimFormula(
        "claimSuperCondensed", "superCondensed");

    private static Formula ClaimFormula(string claimName, string neighborhoodName)
    {
        var alpha = Alpha;
        var n = F.Id("n");
        var d = F.Id("d");
        var a = F.Id("a");
        var w = F.Id("w");
        var unary = Call("replicate", n, a);
        var conclusion = LessOrEqual(
            Cardinality(Call(neighborhoodName, unary, d)),
            Cardinality(Call(neighborhoodName, w, d)));
        var body = ForAll("n", Naturals(),
            ForAll("d", Naturals(),
                ForAll("a", alpha,
                    ForAll("w", ListOf(alpha),
                        Implies(Equal(Length(w), n), conclusion)))));
        return Disp(IffFormula(
            F.Id(claimName),
            WithAlphabet(body, finite: true)));
    }

    private static Formula ResultCondensedFormula() =>
        Disp(new Formula.Not(F.Id("claimCondensed")));

    private static Formula ResultSuperCondensedFormula() =>
        Disp(new Formula.Not(F.Id("claimSuperCondensed")));

    private static Formula WithAlphabet(Formula body, bool finite)
    {
        var alpha = Alpha;
        var typeclasses = finite
            ? Seq(
                OpenBracket, Call("Fintype", alpha), CloseBracket, Comma, Sp,
                OpenBracket, Call("DecidableEq", alpha), CloseBracket, Comma, Sp)
            : Seq(
                OpenBracket, Call("DecidableEq", alpha), CloseBracket, Comma, Sp);
        return Seq(
            Forall, Sp, alpha, Colon, Sp, F.Id("Type"), Comma, Sp,
            typeclasses,
            body);
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            domain,
            body);

    private static Formula SetOf(Formula variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, variable, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula Cons(Formula head, Formula tail) =>
        Call("cons", head, tail);

    private static Formula ListOf(Formula type) => Call("List", type);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Length(Formula value) => Call("length", value);

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.And,
            Parenthesized(right));

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(
            Parenthesized(hypothesis),
            FormulaLogicOperator.Implies,
            Parenthesized(conclusion));

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
