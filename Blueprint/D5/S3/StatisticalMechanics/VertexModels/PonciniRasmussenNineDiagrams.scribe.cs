using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineDiagramsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDi"
                +
                "agrams.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine-strand matching coordinates", H("Nine-strand matching coordinates"), Blocks(
            Paragraph(Text("There are 4862 indexed noncrossing matchings. The actual " +
                "private matching and transitions constants supply the decoded " +
                "involution and literal transition tree. Both tables use " +
                "D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.Tree " +
                "and its shared get function. Circular order" +
                " lists top ports left to right and bottom ports right to left." +
                " Transition value 4862 denotes a loop.")),

            Node("diagram", All("i", Fin(D(4862)), Eq(Call("diagram", X("i")),
                Call("Subtype.mk", Call("toMatching", Call("matching", X("i"))),
                    Call("Exists.intro", Call("matching", X("i")), N("rfl"))))),
                "The subtype pairs the literal matching with its noncrossing representative."),
            Node("transition", All("g", Fin(D(8)), All("i", Fin(D(4862)),
                Eq(Call("transition", X("g"), X("i")), FinMk(TransitionCode(),
                    Call("Nat.mod_lt", Call("Nat.div",
                        Call("get", Call("get", N("transitions"), Val(X("i"))), D(0)),
                        Power(D(4863), Val(X("g")))), OmegaProof()))))),
                "Both operations on the packed transition code are " +
                "natural-number division and remainder."),
            Node("transition_check", All("i", Fin(D(4862)), All("g", Fin(D(8)),
                And(IffOf(Eq(Mate(X("i"), Port(Val(X("g")))), Port(Add(Val(X("g")), D(1)))),
                    Eq(Val(Call("transition", X("g"), X("i"))), D(4862))),
                    All("ht", Less(Val(Call("transition", X("g"), X("i"))), D(4862)),
                        All("x", Call("Boundary", D(9)), Eq(Mate(
                            FinMk(Val(Call("transition", X("g"), X("i"))), X("ht")), X("x")),
                            Call("reconnected", Val(X("g")), OmegaProof(),
                                SubVal(Call("diagram", X("i"))), X("x")))))))),
                "The target is constructed in Fin 4862 using ht. The source " +
                "port indices lie in Fin 9 because g lies in Fin 8.",
                DescribeRole.Theorem),
            Node("unit_check", All("x", Call("Boundary", D(9)),
                Eq(Mate(FinMk(D(4861), OmegaProof()), X("x")),
                    Call("Matching.mate", Call("identityMatching", D(9)), X("x")))),
                "Coordinate 4861 has the mate function of the identity matching.",
                DescribeRole.Theorem))));

    private static Formula TransitionCode() => Call("Nat.mod", Call("Nat.div",
        Call("get", Call("get", N("transitions"), Val(X("i"))), D(0)),
        Power(D(4863), Val(X("g")))), D(4863));
    private static Formula Port(Formula i) => Pair(N("false"), FinMk(i, OmegaProof()));
    private static Formula Mate(Formula i, Formula x) =>
        Call("Matching.mate", SubVal(Call("diagram", i)), x);


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
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) =>
        new Formula.Power(Parenthesized(a), Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula SubVal(Formula x) => Call("Subtype.val", x);
    private static Formula OmegaProof() => Seq(N("by"), Sp, N("omega"));
    private static Formula FinMk(Formula x, Formula proof) => Call("Fin.mk", x, proof);
    private static Formula Pair(Formula a, Formula b) => Call("Prod.mk", a, b);
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
