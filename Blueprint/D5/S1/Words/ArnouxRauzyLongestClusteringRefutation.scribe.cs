using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ArnouxRauzyLongestClusteringRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/ferenczizamboni2024arnouxrauzy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A longer perfectly clustering Arnoux–Rauzy factor refutes the Ferenczi–Zamboni conjecture.",
        H("Longest clustering words in Arnoux–Rauzy languages"),
        Blocks(
            Definition("ar-blocks", "Arnoux–Rauzy blocks", "arBlocks", ArBlocksFormula(),
                "The blocks are generated from the three initial letters by the source's rule at each stage.", Source),
            Definition("infinite-occurrence", "Infinitely often directives", "InfOften", InfOftenFormula(),
                "Every letter occurs at or after every prescribed stage.", Source),
            Definition("rabc", "The condition (Rabc)", "Rabc", RabcFormula(),
                "The source condition says: “the rule at stage 0 is (a), and the first rule different from (a) is (b)”.", Source),
            Definition("arnoux-raouzy-language", "Arnoux–Rauzy language", "arLang", ArLangFormula(),
                "A language contains the finite factors of its directive blocks.", Source),
            Definition("standard-ar-word", "Standard Arnoux–Rauzy words", "IsStandardAR", StandardFormula(),
                "A standard word is one of the directive blocks for a directive using every rule infinitely often.", Source),
            Definition("conjugate-standard", "Conjugacy to a standard word", "ConjugateToStandard", ConjugateFormula(),
                "A word is conjugate to a standard word when one of its rotations is standard.", Source),
            Definition("burrows-wheeler-transform", "The Burrows–Wheeler transform", "bwt", BwtFormula(),
                "The transform is the last column of the sorted conjugates. Bool.not of reverse List.lex compares permutation ranks; List.insertionSort orders the rotations and List.getLast? supplies the last column.", Source),
            Definition("clustering", "Clustering", "IsClustering", ClusteringFormula(),
                "The source calls a word clustering when its transform is a concatenation of constant permutation blocks, and perfectly clustering for the symmetric permutation.", Source),
            Definition("proposition-word", "The word from Proposition 14", "propLongWord", PropWordFormula(),
                "The displayed word is the source's construction from the shortest and middle blocks at the stages determined by (Rabc).", Source),
            Describe.Lean(
                DescribeId.Create("longest-clustering-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Ferenczi–Zamboni Conjecture 1"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Conjecture 1 states verbatim: “In a given AR language Λ satisfying (Rabc), "
                    + "the word in Proposition [14] is the longest clustering word, or, if this fails, "
                    + "the longest clustering word conjugate to a standard AR word.” The formal claim is "
                    + "the weaker second alternative, with Fin 3 letters encoded as 0, 1, and 2 and "
                    + "word length measured by List.length."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("longest-clustering-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A longer perfectly clustering factor exists"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For the directive abcacba(abc)ω, the factor U₁ has length 43, is in the "
                    + "Arnoux–Rauzy language, is perfectly clustering, and is conjugate to a standard "
                    + "word. Its BWT is b¹²c⁷a²⁴ for a<c<b. The Proposition 14 word has length 40, "
                    + "so this factor refutes the asserted longest-word bound. The general value "
                    + "of the longest clustering word remains open."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ferenczi-zamboni-2023-arnoux-rauzy-longest-clustering"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string title, string name, Formula formula,
        string prose, LibraryNoteRef source) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ArBlocksFormula()
    {
        Formula initial = Fun("x", Fin3(), Qualified("List", "singleton", F.Id("x")));
        Formula rule = Call("d", F.Id("j"));
        Formula step = Fun("j", N(), Fun("f", Arrow(Fin3(), ListFin3()),
            Qualified("Function", "update",
                Fun("x", Fin3(), Append(Call("f", F.Id("x")), Call("f", rule))),
                rule, Call("f", rule))));
        return Forall("d", Arrow(N(), Fin3()), Forall("k", N(), Forall("x", Fin3(),
            Equal(Call("arBlocks", F.Id("d"), F.Id("k"), F.Id("x")),
                Qualified("Nat", "rec", initial, step, F.Id("k"), F.Id("x"))))));
    }

    private static Formula InfOftenFormula() =>
        Forall("d", Arrow(N(), Fin3()), Iff(Call("InfOften", F.Id("d")),
            Forall("x", Fin3(), Forall("N", N(), Exists("k", N(),
                And(LessEqual(F.Id("N"), F.Id("k")), Equal(Call("d", F.Id("k")), F.Id("x"))))))));

    private static Formula RabcFormula() =>
        Forall("d", Arrow(N(), Fin3()), Iff(Call("Rabc", F.Id("d")),
            And(Equal(Call("d", D(0)), D(0)), Exists("k", N(),
                And(NotEqual(Call("d", F.Id("k")), D(0)),
                    And(Forall("j", N(), Imply(Less(F.Id("j"), F.Id("k")),
                            Equal(Call("d", F.Id("j")), D(0)))),
                        Equal(Call("d", F.Id("k")), D(1))))))));

    private static Formula ArLangFormula()
    {
        Formula factor = Exists("k", N(), Exists("x", Fin3(),
            Qualified("List", "IsInfix", F.Id("w"),
                Call("arBlocks", F.Id("d"), F.Id("k"), F.Id("x")))));
        Formula set = SetBuilder("w", ListFin3(), factor);
        return Forall("d", Arrow(N(), Fin3()), Equal(Call("arLang", F.Id("d")), set));
    }

    private static Formula StandardFormula()
    {
        Formula block = Exists("k", N(), Exists("x", Fin3(),
            Equal(F.Id("w"), Call("arBlocks", F.Id("d"), F.Id("k"), F.Id("x")))));
        Formula body = And(Call("InfOften", F.Id("d")), block);
        return Forall("w", ListFin3(), Iff(Call("IsStandardAR", F.Id("w")),
            Exists("d", Arrow(N(), Fin3()), body)));
    }

    private static Formula ConjugateFormula() =>
        Forall("w", ListFin3(), Iff(Call("ConjugateToStandard", F.Id("w")),
            Exists("r", N(), Call("IsStandardAR", Qualified("List", "rotate", F.Id("w"), F.Id("r"))))));

    private static Formula BwtFormula()
    {
        Formula words = Call("List", ListFin3());
        Formula lt = Fun("x", Fin3(), Fun("y", Fin3(),
            Call("decide", Less(Call("o", F.Id("x")), Call("o", F.Id("y"))))));
        Formula comparison = Fun("a", ListFin3(), Fun("b", ListFin3(),
            Equal(Qualified("Bool", "not", Qualified("List", "lex", F.Id("b"), F.Id("a"), lt)), F.Id("true"))));
        Formula rhs = Let("rs", words, Qualified("List", "map",
                Fun("i", N(), Qualified("List", "rotate", F.Id("w"), F.Id("i"))),
                Qualified("List", "range", Qualified("List", "length", F.Id("w")))),
            Let("sr", words, Qualified("List", "insertionSort", comparison, F.Id("rs")),
                Qualified("List", "filterMap", QualifiedLast(), F.Id("sr"))));
        return Forall("o", EquivPerm3(), Forall("w", ListFin3(), Equal(Call("bwt", F.Id("o"), F.Id("w")), rhs)));
    }

    private static Formula ClusteringFormula()
    {
        Formula letters = Qualified("List", "ofFn", Qualified("Equiv", "symm", F.Id("o")));
        Formula block = Fun("l", Fin3(), Qualified("List", "replicate",
            Qualified("List", "count", Call("pi", F.Id("l")), F.Id("w")), Call("pi", F.Id("l"))));
        Formula target = Qualified("List", "flatMap", block, letters);
        return Forall("w", ListFin3(), Iff(Call("IsClustering", F.Id("w")),
            Exists("o", EquivPerm3(), Exists("pi", EquivPerm3(),
                And(NotEqual(F.Id("pi"), D(1)), Equal(Call("bwt", F.Id("o"), F.Id("w")), target))))));
    }

    private static Formula PropWordFormula()
    {
        Formula occurrence = Exists("k", N(),
            And(LessEqual(F.Id("start"), F.Id("k")), Equal(Call("d", F.Id("k")), F.Id("x"))));
        Formula firstAt = Fun("d", Arrow(N(), Fin3()), Fun("x", Fin3(), Fun("start", N(),
            Seq(Keyword("if"), Sp, F.Id("h"), Sp, Colon, Sp, occurrence,
                Sp, Keyword("then"), Sp, Qualified("Nat", "find", F.Id("h")),
                Sp, Keyword("else"), Sp, D(0)))));
        Formula mu = Qualified("Nat", "findGreatest", Fun("j", N(),
            NotEqual(Call("d", Subtract(F.Id("j"), D(1))),
                Call("d", Subtract(F.Id("muy"), D(1))))), F.Id("muy"));
        Formula blocks = Qualified("List", "ofFn", Call("arBlocks", F.Id("d"), F.Id("muy")));
        Formula rhs = Let("firstAt", Arrow(Arrow(N(), Fin3()), Arrow(Fin3(), Arrow(N(), N()))), firstAt,
            Let("lam2", N(), Call("firstAt", F.Id("d"), D(2), D(0)),
                    Let("mua", N(), Call("firstAt", F.Id("d"), D(0), Add(F.Id("lam2"), D(1))),
                        Let("mub", N(), Call("firstAt", F.Id("d"), D(1), Add(F.Id("lam2"), D(1))),
                            Let("muy", N(), If(Less(F.Id("mua"), F.Id("mub")), F.Id("mub"), F.Id("mua")),
                                Let("mu", N(), mu,
                                    Let("sb", Call("List", ListFin3()), Qualified("List", "insertionSort",
                                            Fun("u", ListFin3(), Fun("v", ListFin3(),
                                                LessEqual(Qualified("List", "length", F.Id("u")), Qualified("List", "length", F.Id("v"))))), blocks),
                                        Let("S", ListFin3(), Qualified("List", "getD", F.Id("sb"), D(0), List()),
                                            Let("M", ListFin3(), Qualified("List", "getD", F.Id("sb"), D(1), List()),
                                                Append(Qualified("List", "flatten", Qualified("List", "replicate",
                                                        Add(Subtract(F.Id("muy"), F.Id("mu")), D(1)), F.Id("S"))),
                                                    F.Id("M")))))))))));
        return Forall("d", Arrow(N(), Fin3()), Equal(Call("propLongWord", F.Id("d")), rhs));
    }

    private static Formula ClaimFormula() =>
        Iff(F.Id("claim"), Forall("d", Arrow(N(), Fin3()),
            Imply(Call("Rabc", F.Id("d")),
                Imply(Call("InfOften", F.Id("d")),
                    Forall("w", ListFin3(),
                        Imply(new Formula.Relation(F.Id("w"), FormulaRelationOperator.MemberOf,
                                Call("arLang", F.Id("d"))),
                            Imply(Call("IsClustering", F.Id("w")),
                                Imply(Call("ConjugateToStandard", F.Id("w")),
                                    LessEqual(Qualified("List", "length", F.Id("w")),
                                        Qualified("List", "length", Call("propLongWord", F.Id("d"))))))))))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin3() => Call("Fin", D(3));
    private static Formula ListFin3() => Call("List", Fin3());
    private static Formula EquivPerm3() => Qualified("Equiv", "Perm", Fin3());
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Keyword(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Fun(string name, Formula domain, Formula body) =>
        Seq(Keyword("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, domain)), Sp, Mapsto, Sp, body);
    private static Formula Let(string name, Formula type, Formula value, Formula body, bool recursive = false) =>
        new Formula.Aligned([
            Seq(Keyword("let"), Sp, recursive ? Seq(Keyword("rec"), Sp) : Sp,
                F.Id(name), Sp, Colon, Sp, type, Sp, Colon, Eq, Sp, value, Semi),
            body]);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Keyword("if"), Sp, Parenthesized(condition), Sp, Keyword("then"), Sp, yes, Sp, Keyword("else"), Sp, no);
    private static Formula Match(Formula value, params (Formula Pattern, Formula Value)[] branches) =>
        Seq(Keyword("match"), Sp, value, Sp, Keyword("with"), Sp,
            new Formula.Aligned([.. branches.Select(branch => Seq(Bar, Sp, branch.Pattern, Sp, Mapsto, Sp, branch.Value))]));
    private static Formula List(params Formula[] values) => values.Length == 0
        ? Seq(OpenBracket, CloseBracket)
        : Seq(OpenBracket, Seq([.. values.SelectMany((value, i) => i == 0 ? new[] { value } : new[] { Comma, Sp, value })]), CloseBracket);
    private static Formula Cons(Formula head, Formula tail) => Qualified("List", "cons", head, tail);
    private static Formula Append(Formula left, Formula right) => Qualified("List", "append", left, right);
    private static Formula QualifiedLast() => Fun("l", ListFin3(), Match(F.Id("l"),
        (List(), F.Id("none")),
        (Cons(F.Id("a"), F.Id("as")), Call("some", Qualified("List", "getLast", Cons(F.Id("a"), F.Id("as")))))));
    private static Formula Add(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Plus, Sp, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Minus, Sp, Parenthesized(right));
    private static Formula Forall(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula SetBuilder(string name, Formula domain, Formula body) =>
        Seq(OpenBrace, F.Id(name), Colon, domain, Sp, Bar, Sp, body, CloseBrace);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imply(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
