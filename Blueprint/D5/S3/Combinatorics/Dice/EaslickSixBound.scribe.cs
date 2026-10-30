using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class EaslickSixBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/EaslickSixBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/easlick2026minimaldice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete dice conjecture follows from an exhaustive six-face upper bound and uniform longer cycles.",
        H("EaslickSixBound"),
        Blocks(
            Node("easlick-check-rank", "Arbitrary finite graph rank certificate checker", "checkRank",
                "Input consists of any finite vertex list, an executable Boolean edge function, a natural rank function, finite rank fibers, a collision triple for each rank, and a proposed bound b. For every input vertex the checker tests membership in its supplied fiber, absence of duplicates, capacity at most b+1, and weak rank decrease on every input edge. Each fiber must either have size at most b or supply two distinct member vertices whose every internal outgoing edge has the same target. These are executable checks, not assumed graph laws. The checker may reject certificates for graphs whose cycles nevertheless satisfy the bound; only soundness is asserted."),
            Node("easlick-check-rank-sound", "General rank checker soundness", "checkRank_sound",
                "For an arbitrary decidable inhabited vertex type and all checker inputs, a successful Boolean check bounds the length of every nonempty simple closed edge chain contained in the input vertex list by b. The proof derives constancy of rank around the cycle, containment in one rank fiber, and the capacity bound. If the capacity is b+1 and a longer cycle existed, it would exhaust that fiber and force equal successors at two distinct positions, contradicting successor injectivity. No law of the graph is a hypothesis beyond the executable check and the given cycle's defining conditions."),
            Node("easlick-six-rank-check", "Actual first rank checker input", "sixRank_check",
                "The complete recursive enumeration of six-face dice, exact score-19 Boolean edges, retained rank and fiber tables, and the two collision triples pass the arbitrary-input checker with bound six by kernel reduction. This is the actual computed first instance. Every numeric and checking premise is discharged. six_cycle_bound consumes checkRank_sound applied to this successful check, and S_six and conjecture_one consume that universal conclusion."),
            Node("easlick-six-cycle-bound", "The global six-face upper bound", "six_cycle_bound",
                "For every natural k, HasCycle(6,k) implies k at most six. A complete recursive enumeration includes all 462 sorted six-face dice with labels from one through six, including repetitions and the standard die. Every score-19 edge weakly decreases the certified rank. A closed cycle therefore has one rank and lies in its entire rank fiber. All fibers have at most seven elements. In each seven-element fiber, two distinct vertices have the same unique internal successor. A seven-cycle would exhaust that fiber, contradicting injectivity of the cyclic successor operation on distinct vertices. The certificate is checked by Lean kernel reduction; its rank data are a witness, never an assumed law."),
            Node("easlick-s-six", "The attained six-face maximum", "S_six",
                "S(6) holds: an explicit six-cycle attains the global upper bound of six. The upper bound applies to every simple directed cycle in the full graph at the true least attainable strict-win probability above one half."),
            Node("easlick-conjecture-one", "The complete Easlick conjecture", "conjecture_one",
                "The complete proposition is S(6) and, for every natural n at least seven, not S(n). Natural n faithfully represents the source integer range n at least three. Dice are all nondecreasing lists of n labels in the interval from one through n. Repeated faces and the standard tuple remain included. Strict-win probability is unconditional on the uniform independent product of face indices. The attained minimum is proved, not taken from the author parity formula. S quantifies over all longer simple cycles, with no finite cutoff.")
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(F.Disp(Statement(declaration))),
            declaration is "six_cycle_bound" or "S_six" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose)), Paragraph(Text("In these formulas, at is zero-based list indexing, length and dedup are list length and duplicate removal, head is Lean head!, fst and snd are product projections, and List subset means membership inclusion. dice6, rank6, fiber6 and cuts6 are the private Lean inputs; decide converts the displayed decidable proposition to Bool. The checker definitions are characterized by equality to the Boolean value true, including empty-input behavior. All quantifiers include their full carrier types and anonymous instance dictionaries."))), declaration == "checkRank" ? DescribeRole.Definition : DescribeRole.Theorem,
            declaration == "conjecture_one"
                ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("easlick-2026-minimal-advantage-cycle-conjecture-one"), ResolutionKind.Proved)
                : null);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(a, FormulaLogicOperator.And,b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula N => Id("Nat");
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Or,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Arrow(Formula a, Formula b) => F.Seq(F.Open,a,F.Sp,F.To,F.Sp,b,F.Close);
    private static Formula Product(Formula a, Formula b) => F.Seq(F.Open,a,F.Sp,F.Times,F.Sp,b,F.Close);
    private static Formula Fn(string name, Formula type, Formula body) => F.Seq(F.LambdaLower,F.Sp,F.Open,Id(name),F.Colon,type,F.Close,F.Sp,F.Mapsto,F.Sp,body);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f,[.. args]);
    private static Formula Len(Formula c) => Call("length",c);
    private static Formula Instance(string name, Formula a, Formula body) => F.Seq(F.OpenBracket,Call(name,a),F.CloseBracket,F.Comma,F.Sp,body);
    private static Formula RankStatement(bool sound)
    {
        Formula a=Id("A"),v=Id("V"),e=Id("E"),r=Id("r"),f=Id("F"),w=Id("W"),b=Id("b"),d=Id("d"),x=Id("x"),c=Id("c"),t=Id("true");
        Formula fiber=App(f,App(r,d)),cut=App(w,App(r,d));
        Formula first=Call("fst",cut),second=Call("fst",Call("snd",cut)),target=Call("snd",Call("snd",cut));
        Formula row=And(Mem(d,fiber),Equal(Len(Call("dedup",fiber)),Len(fiber)),Le(Len(fiber),Add(b,Num(1))),
            All(Imp(And(Mem(x,v),Equal(App(e,d,x),t)),Le(App(r,x),App(r,d))),B("x",a)),
            Or(Le(Len(fiber),b),And(Mem(first,fiber),Mem(second,fiber),NotEqual(first,second),
                All(Imp(Mem(x,fiber),And(Imp(Equal(App(e,first,x),t),Equal(x,target)),Imp(Equal(App(e,second,x),t),Equal(x,target)))),B("x",a)))));
        Formula check=Equal(Call("checkRank",v,e,r,f,w,b),t);
        Formula body=sound
            ? All(Imp(And(check,Call("Nodup",c),NotEqual(c,Call("nil")),new Formula.Relation(c,FormulaRelationOperator.SubsetOf,v),
                Call("IsChain",Fn("u",a,Fn("z",a,Equal(App(e,Id("u"),Id("z")),t))),Call("append",c,Call("singleton",Call("head",c))))),Le(Len(c),b)),B("c",Call("List",a)))
            : Iff(check,All(Imp(Mem(d,v),row),B("d",a)));
        body=All(body,B("V",Call("List",a)),B("E",Arrow(a,Arrow(a,Id("Bool")))),B("r",Arrow(a,N)),B("F",Arrow(N,Call("List",a))),B("W",Arrow(N,Product(a,Product(a,a)))),B("b",N));
        if(sound) body=Instance("Inhabited",a,body);
        return All(Instance("DecidableEq",a,body),B("A",Id("Type")));
    }
    private static Formula Statement(string declaration) => declaration switch
    {
        "checkRank" => RankStatement(false),
        "checkRank_sound" => RankStatement(true),
        "sixRank_check" => Equal(Call("checkRank",Id("dice6"),Fn("d",Call("List",N),Fn("e",Call("List",N),Call("decide",Equal(Call("winCount",Id("d"),Id("e")),Num(19))))),Id("rank6"),Id("fiber6"),Id("cuts6"),Num(6)),Id("true")),
        "six_cycle_bound" => All(Imp(Call("HasCycle",Num(6),Id("k")),Le(Id("k"),Num(6))),B("k",N)),
        "S_six" => Call("S",Num(6)),
        "conjecture_one" => And(Call("S",Num(6)),All(Imp(Le(Num(7),Id("n")),Not(Call("S",Id("n")))),B("n",N))),
        _ => throw new ArgumentException("Unknown dice declaration",nameof(declaration))
    };

}
