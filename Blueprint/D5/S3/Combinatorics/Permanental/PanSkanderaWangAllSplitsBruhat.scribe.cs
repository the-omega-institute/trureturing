using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsBruhatDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The operator sum adds over the finite domain of its function.",
        H("PanSkanderaWangAllSplitsBruhat"),
        Blocks(
            Node("rankf", "rankF", "rankF",
                rankFFormula(),
                "The operator sum adds over the finite domain of its function. This integer-valued prefix rank counts positions below p whose zero-based permutation values are at least q.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rankle", "RankLE", "RankLE",
                RankLEFormula(),
                "Rank domination compares every prefix length and every value threshold.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("upstep", "UpStep", "UpStep",
                UpStepFormula(),
                "A generating upward edge swaps increasing positions whose values are increasing. Multiplication is permutation composition in the Lean convention.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("rank-lifting-step", "rank lifting step", "rank_lifting_step",
                rankliftingstepFormula(),
                "If the earlier positions agree and no intervening source value lies in the stated interval, the indicated upward transposition remains below u in every prefix rank. The rank-gap count supplies the extra unit when a threshold crosses the swapped values.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("exists-lifting-step", "exists lifting step", "exists_lifting_step",
                existsliftingstepFormula(),
                "Distinct rank-comparable permutations admit an upward transposition that preserves domination by the upper permutation. The first differing position and the first admissible later value determine the step.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("rank-to-chain", "rank to chain", "rank_to_chain",
                ranktochainFormula(),
                "Every rank comparison is realized by a finite reflexive transitive chain of upward swaps. The position-value score decreases strictly at each chosen lifting step, which terminates the construction.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula rankFFormula() => Disp(
        All("n", Naturals(), All("w", Call("Perm", Call("Fin", F.Id("n"))), All("p", Naturals(), All("q", Naturals(), Equal(Call("rankF", F.Id("w"), F.Id("p"), F.Id("q")), Call("sum", LambdaOf("k", Call("Fin", F.Id("n")), Call("ite", And(LessThan(Call("val", F.Id("k")), F.Id("p")), LessEqual(F.Id("q"), Call("val", App(F.Id("w"), F.Id("k"))))), Parenthesized(Seq(D(1), Sp, Colon, Sp, Integers())), Parenthesized(Seq(D(0), Sp, Colon, Sp, Integers())))))))))));

    private static Formula RankLEFormula() => Disp(
        All("n", Naturals(), All("w", Call("Perm", Call("Fin", F.Id("n"))), All("u", Call("Perm", Call("Fin", F.Id("n"))), Iff(Call("RankLE", F.Id("w"), F.Id("u")), All("p", Naturals(), All("q", Naturals(), LessEqual(Call("rankF", F.Id("w"), F.Id("p"), F.Id("q")), Call("rankF", F.Id("u"), F.Id("p"), F.Id("q"))))))))));

    private static Formula UpStepFormula() => Disp(
        All("n", Naturals(), All("w", Call("Perm", Call("Fin", F.Id("n"))), All("v", Call("Perm", Call("Fin", F.Id("n"))), Iff(Call("UpStep", F.Id("w"), F.Id("v")), Exists("i", Call("Fin", F.Id("n")), Exists("j", Call("Fin", F.Id("n")), And(LessThan(F.Id("i"), F.Id("j")), LessThan(App(F.Id("w"), F.Id("i")), App(F.Id("w"), F.Id("j"))), Equal(F.Id("v"), Multiply(F.Id("w"), Call("swap", F.Id("i"), F.Id("j"))))))))))));

    private static Formula rankliftingstepFormula() => Disp(
        All("n", Naturals(), All("w", Call("Perm", Call("Fin", F.Id("n"))), All("u", Call("Perm", Call("Fin", F.Id("n"))), All("i", Call("Fin", F.Id("n")), All("j", Call("Fin", F.Id("n")), Implies(And(LessThan(F.Id("i"), F.Id("j")), LessThan(App(F.Id("w"), F.Id("i")), App(F.Id("w"), F.Id("j"))), LessEqual(App(F.Id("w"), F.Id("j")), App(F.Id("u"), F.Id("i"))), All("k", Call("Fin", F.Id("n")), Implies(LessThan(F.Id("k"), F.Id("i")), Equal(App(F.Id("w"), F.Id("k")), App(F.Id("u"), F.Id("k"))))), All("k", Call("Fin", F.Id("n")), Implies(LessThan(F.Id("i"), F.Id("k")), Implies(LessThan(F.Id("k"), F.Id("j")), Not(And(LessThan(App(F.Id("w"), F.Id("i")), App(F.Id("w"), F.Id("k"))), LessEqual(App(F.Id("w"), F.Id("k")), App(F.Id("u"), F.Id("i")))))))), Call("RankLE", F.Id("w"), F.Id("u"))), Call("RankLE", Multiply(F.Id("w"), Call("swap", F.Id("i"), F.Id("j"))), F.Id("u")))))))));

    private static Formula existsliftingstepFormula() => Disp(
        All("n", Naturals(), All("w", Call("Perm", Call("Fin", F.Id("n"))), All("u", Call("Perm", Call("Fin", F.Id("n"))), Implies(Call("RankLE", F.Id("w"), F.Id("u")), Implies(NotEqual(F.Id("w"), F.Id("u")), Exists("v", Call("Perm", Call("Fin", F.Id("n"))), And(Call("UpStep", F.Id("w"), F.Id("v")), Call("RankLE", F.Id("v"), F.Id("u"))))))))));

    private static Formula ranktochainFormula() => Disp(
        All("n", Naturals(), All("w", Call("Perm", Call("Fin", F.Id("n"))), All("u", Call("Perm", Call("Fin", F.Id("n"))), Implies(Call("RankLE", F.Id("w"), F.Id("u")), Call("ReflTransGen", F.Id("UpStep"), F.Id("w"), F.Id("u")))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula LambdaOf(string name, Formula domain, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, domain)),
            Sp, Mapsto, Sp, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Integers() => Seq(Mathbb, Sp, Grp(F.Id("Z")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Not(Formula value) => Seq(Neg, Sp, Parenthesized(value));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }}
