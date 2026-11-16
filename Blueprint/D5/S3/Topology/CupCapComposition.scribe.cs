using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class CupCapCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/CupCapComposition.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generator paths and internal components", H("Generator paths and internal components"),
                Blocks(
            Paragraph(Text("For j+1<n, the generator ports are the literal elements " +
                "(false,Fin.mk j _) and (false,Fin.mk (j+1) hj) of Boundary n. " +
                "The generator pairs these ports and reconnects their former " +
                "partners.")),

            Node("reconnected", Scope(All("x", Call("Boundary", X("n")),
                Eq(Call("reconnected", X("j"), X("hj"), X("d"), X("x")),
                    If(Eq(X("x"), LeftPort()), RightPort(),
                        If(Eq(X("x"), RightPort()), LeftPort(),
                            If(Eq(Mate(X("x")), LeftPort()), Mate(RightPort()),
                If(Eq(Mate(X("x")), RightPort()), Mate(LeftPort()), Mate(X("x"))))))))),
                "The four tests are the literal defining conditional, with both" +
                " boundary ports expanded."),
            Node("composite_cupcap_mate", Scope(All("x", Call("Boundary", X("n")),
                Eq(Call("Matching.mate", Call("composite", Cupcap(), X("d")), X("x")),
                    Call("reconnected", X("j"), X("hj"), X("d"), X("x"))))),
                "The reconnected mate is the endpoint reached by the sewn path.",
                DescribeRole.Theorem),
            Node("internalLoopCount_cupcap_zero", Scope(Arrow(Ne(Mate(LeftPort()), RightPort()),
                Eq(Loops(), D(0)))),
                "If the inputs are not paired, every component reaches an " +
                "exposed endpoint.", DescribeRole.Theorem),
            Node("internalLoopCount_cupcap_pos", Scope(Arrow(Eq(Mate(LeftPort()), RightPort()),
                Less(D(0), Loops()))),
                "Paired inputs close an internal component.", DescribeRole.Theorem),
            Node("internalLoopCount_cupcap_eq_zero_iff", Scope(IffOf(Eq(Loops(), D(0)),
                Ne(Mate(LeftPort()), RightPort()))),
                "This is the exact zero-loop criterion for a generator product.",
                DescribeRole.Theorem))));

    private static Formula Scope(Formula body) => All("n", Nat(), All("j", Nat(),
        All("hj", Less(Add(X("j"), D(1)), X("n")),
            All("d", Call("Matching", Call("Boundary", X("n"))), body))));
    private static Formula LeftPort() => Pair(N("false"), FinMk(X("j"), OmegaProof()));
    private static Formula RightPort() => Pair(N("false"), FinMk(Add(X("j"), D(1)), X("hj")));
    private static Formula Mate(Formula x) => Call("Matching.mate", X("d"), x);
    private static Formula Cupcap() => Call("cupcapMatching", X("j"), X("hj"));
    private static Formula Loops() => Call("internalLoopCount", Cupcap(), X("d"));


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
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula If(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Nat() => N("Nat");
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
