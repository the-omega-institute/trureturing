using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfCharacterizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfCharacterization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two patterns are characterized by increasing pairs on opposite sides of a fixed point of the inverse Foata map.",
        H("Fixed Points and the Two Avoidance Conditions"),
        Blocks(
            Node("contains-twelve", "Occurrences of the first pattern", "contains_twelve_iff",
                OccurrenceFormula(false),
                "The first pattern occurs precisely when two entries a and b appear in increasing order below a larger entry f fixed by hat; all three entries belong to the word.", DescribeRole.Theorem),
            Node("contains-twenty-three", "Occurrences of the second pattern", "contains_twenty_three_iff",
                OccurrenceFormula(true),
                "The second pattern occurs precisely when two entries a and b appear in increasing order above a smaller entry f fixed by hat; all three entries belong to the word.", DescribeRole.Theorem),
            Node("fixed-point-characterization", "Singleton blocks and fixed points", "hat_fixed_iff",
                FixedFormula(),
                "For a word with distinct entries containing f, hat fixes f exactly when f starts a left-to-right-maximum block and either ends the word or is followed by an entry larger than f.", DescribeRole.Theorem),
            Node("pair-sublist-total", "Either order occurs", "pair_sublist_total", null,
                "For two distinct entries of a list without repeated entries, at least one of their two orders occurs as a sublist.", DescribeRole.Theorem),
            Node("pair-sublist-asymmetry", "The two orders are incompatible", "pair_sublist_asymm", null,
                "A list without repeated entries cannot contain both ordered two-entry sublists on distinct entries.", DescribeRole.Theorem),
            Node("avoid-twelve", "Avoidance below fixed points", "avoids_twelve_iff",
                AvoidanceFormula(false),
                "A word with distinct entries avoids the first pattern exactly when every pair of entries below each hat-fixed value appears in decreasing order.", DescribeRole.Theorem),
            Node("avoid-twenty-three", "Avoidance above fixed points", "avoids_twenty_three_iff",
                AvoidanceFormula(true),
                "A word with distinct entries avoids the second pattern exactly when every pair of entries above each hat-fixed value appears in decreasing order.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula OccurrenceFormula(bool upper)
    {
        var p = F.Id("p"); var a = F.Id("a"); var b = F.Id("b"); var f = F.Id("f");
        var pattern = upper ? Pattern(D(2), D(3), D(1)) : Pattern(D(1), D(2), D(3));
        var body = And(upper ? Lt(f, a) : Lt(a, b), upper ? Lt(a, b) : Lt(b, f),
            Mem(a, p), Mem(b, p), Mem(f, p),
            Call("Sublist", Seq(OpenBracket, a, Comma, Sp, b, CloseBracket), p),
            Eq(Call("hat", p, f), f));
        return Disp(All("p", Call("List", Nat()), Iff(Call("Contains", pattern.Item1,
            pattern.Item2, D(3), p),
            ExistsMany([Bound("a"), Bound("b"), Bound("f")], body))));
    }

    private static (Formula, Formula) Pattern(Formula first, Formula second, Formula fixedRank) =>
        (Seq(OpenBracket, first, Comma, Sp, second, CloseBracket),
            Seq(OpenBracket, Open, fixedRank, Comma, Sp, fixedRank, Close, CloseBracket));

    private static Formula FixedFormula()
    {
        var p = F.Id("p"); var f = F.Id("f"); var i = Call("idxOf", p, f);
        var next = new Formula.Binary(i, FormulaBinaryOperator.Add, D(1));
        return Disp(All("p", Call("List", Nat()), All("f", Nat(),
            Imp(And(Call("Nodup", p), Mem(f, p)),
                Iff(Eq(Call("hat", p, f), f), And(Call("IsLtrMax", p, i),
                    Or(Eq(next, Call("length", p)), Lt(f, Call("getD", p, next, D(0))))))))));
    }

    private static Formula AvoidanceFormula(bool upper)
    {
        var p = F.Id("p"); var f = F.Id("f"); var a = F.Id("a"); var b = F.Id("b");
        var pattern = upper ? Pattern(D(2), D(3), D(1)) : Pattern(D(1), D(2), D(3));
        var pair = All("a", Nat(), All("b", Nat(), Imp(
            And(upper ? Lt(f, a) : Lt(a, b), upper ? Lt(a, b) : Lt(b, f),
                Mem(a, p), Mem(b, p)),
            Call("Sublist", Seq(OpenBracket, b, Comma, Sp, a, CloseBracket), p))));
        return Disp(All("p", Call("List", Nat()), Imp(Call("Nodup", p),
            Iff(new Formula.Not(Call("Contains", pattern.Item1, pattern.Item2, D(3), p)),
                All("f", Nat(), Imp(And(Mem(f, p), Eq(Call("hat", p, f), f)), pair))))));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula.BoundVariable Bound(string name) => new(FormulaIdentifier.Create(name), Nat());
    private static Formula ExistsMany(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula And(params Formula[] parts)
    {
        Formula result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
}
