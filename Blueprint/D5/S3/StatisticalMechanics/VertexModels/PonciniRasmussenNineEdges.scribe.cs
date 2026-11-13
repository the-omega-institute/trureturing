using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineEdgesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
                "D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges." ;
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reindexing the generator edges", H("Reindexing the generator edges"), Blocks(
            Paragraph(Text("Incoming and outgoing edges are pairs of a Fin 4862 target and" +
                " a Fin 8192 source. Lists preserve multiplicity. Their " +
                "permutation identity reindexes the integer scalar sum in every" +
                " additive commutative group.")),

            Node("incoming", All("i", Fin(D(8192)), Eq(Call("incoming", X("i")),
                Call("D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get",
                    N("D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner.rows"),
                    Val(X("i"))))),
                "The lookup uses the shared " +
                "D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get and " +
                "the single D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner.rows " +
                "table. The index i has " +
                "type Fin 8192 and the returned list has type List Nat."),
            Node("sparseHamiltonian_eq", All("v", Vector(), Eq(Call("sparseHamiltonian", X("v")),
                Fn("i", Fin(D(8192)), IncomingFold()))),
                "List.foldl adds the coefficient at each source index, then the" +
                " Hamiltonian negates the sum.",
                DescribeRole.Theorem),
            Node("incomingEdges", Eq(N("incomingEdges"), Call("List.flatMap",
                Fn("t", Fin(D(4862)), Call("List.map", Fn("s", Nat(),
                    Pair(X("t"), ModIndex(X("s")))),
                    Call("incoming", Embed(X("t"))))), Call("List.finRange", D(4862)))),
                "Each source in a target row is reduced modulo 8192 with " +
                "Nat.mod_lt providing the bound."),
            Node("outgoingEdges", Eq(N("outgoingEdges"), Call("List.flatMap",
                Fn("s", Fin(D(4862)), Call("List.filterMap", Fn("g", Fin(D(8)),
                    Dite("ht", TransitionBound(), Call("Option.some",
                        Pair(FinMk(Val(Transition()), X("ht")), Embed(X("s")))),
                        N("Option.none"))), Call("List.finRange", D(8)))),
                Call("List.finRange", D(4862)))),
                "Only transitions with value below 4862 contribute an edge."),
            Node("edges_perm", Call("List.Perm", N("incomingEdges"), N("outgoingEdges")),
                "Both lists enumerate the same edges with the same multiplicities.",
                DescribeRole.Theorem),
            Node("sparse_sum", Group(All("b", Arrow(Fin(D(4862)), X("A")), All("v", Vector(),
                Eq(SumOver("t", Fin(D(4862)), Smul(
                    At(Call("sparseHamiltonian", X("v")), Embed(X("t"))), At(X("b"), X("t")))),
                    Negate(SumOver("s", Fin(D(4862)), SumOver("g", Fin(D(8)),
                        Dite("ht", TransitionBound(), Smul(At(X("v"), Embed(X("s"))),
                            At(X("b"), FinMk(Val(Transition()), X("ht")))), D(0))))))))),
                "Finset.sum binds t, s and g at their stated finite types. Both" +
                " Fin embeddings and the target proof ht are explicit.",
                DescribeRole.Theorem))));

    private static Formula ModIndex(Formula s) => FinMk(Call("Nat.mod", s, D(8192)),
        Call("Nat.mod_lt", s, OmegaProof()));
    private static Formula IncomingFold() => Negate(Call("List.foldl",
        Fn("s", IntType(), Fn("j", Nat(), Add(X("s"), At(X("v"), ModIndex(X("j")))))),
        D(0), Call("incoming", X("i"))));
    private static Formula Transition() => Call("transition", X("g"), X("s"));
    private static Formula TransitionBound() => Less(Val(Transition()), D(4862));


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
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula Dite(string name, Formula c, Formula a, Formula b) =>
        Call("dite", c, Fn(name, c, a), Call("Function.const", Call("Not", c), b));
    private static Formula Nat() => N("Nat");
    private static Formula IntType() => N("Int");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula OmegaProof() => Seq(N("by"), Sp, N("omega"));
    private static Formula FinMk(Formula x, Formula proof) => Call("Fin.mk", x, proof);
    private static Formula Embed(Formula x) =>
        Typed(FinMk(Val(x), OmegaProof()), Fin(D(8192)));
    private static Formula Pair(Formula a, Formula b) => Call("Prod.mk", a, b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Call("Finset.sum", Call("Finset.univ"), Fn(name, type, body));
    private static Formula Smul(Formula a, Formula b) => Call("HSMul.hSMul", a, b);
    private static Formula Group(Formula body) => All("A", N("Type"),
        Seq(OpenBracket, Call("AddCommGroup", X("A")), CloseBracket, Sp, body));
    private static Formula Vector() => Arrow(Fin(D(8192)), IntType());
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
