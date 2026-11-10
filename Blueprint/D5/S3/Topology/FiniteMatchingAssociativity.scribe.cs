using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteMatchingAssociativityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/FiniteMatchingAssociativity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Associative matching sewing", H("Associative matching sewing"), Blocks(
            Paragraph(Text("Boundary n is Bool times Fin n. Composite pairs exposed " +
                "endpoints through the glued middle boundary. The internal loop" +
                " count counts connected components that avoid every exposed " +
                "endpoint. No planarity assumption is used.")),

            Node("composite_assoc", Triple(Eq(Call("composite", Call("composite", X("d"), X("e")),
                X("f")),
                Call("composite", X("d"), Call("composite", X("e"), X("f"))))),
                "Both bracketings induce the same exterior equivalence relation.",
                DescribeRole.Theorem),
            Node("internalLoopCount_cocycle", Triple(Eq(Add(Loops(X("d"), X("e")),
                Loops(Call("composite", X("d"), X("e")), X("f"))),
                Add(Loops(X("e"), X("f")), Loops(X("d"), Call("composite", X("e"), X("f")))))),
                "Both sums count the closed components of the triple gluing.",
                DescribeRole.Theorem),
            Node("internalLoopCount_pos_assoc", Triple(IffOf(
                Or(Less(D(0), Loops(X("d"), X("e"))),
                    Less(D(0), Loops(Call("composite", X("d"), X("e")), X("f")))),
                Or(Less(D(0), Loops(X("e"), X("f"))),
                    Less(D(0), Loops(X("d"), Call("composite", X("e"), X("f"))))))),
                "A closed component occurs in one bracketing exactly when one " +
                "occurs in the other.",
                DescribeRole.Theorem))));

    private static Formula Triple(Formula body) => All("n", Nat(),
        All("d", Matchings(), All("e", Matchings(), All("f", Matchings(), body))));
    private static Formula Matchings() => Call("Matching", Call("Boundary", X("n")));
    private static Formula Loops(Formula a, Formula b) => Call("internalLoopCount", a, b);


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
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
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
