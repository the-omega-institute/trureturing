using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CounterSequences;

internal sealed class KimberlingA371279Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CounterSequences/KimberlingA371279.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/kimberling2024a371279a371280");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every rational in (0,1] occurs exactly once in Kimberling's ordered fraction enumeration.",
        H("Kimberling A371279/A371280: one fraction enumeration"),
        Blocks(
            Paragraph(Text("All arithmetic is exact rational arithmetic. Write C(n) for cumulative(n), "
                + "so C(0) is the source's U(1). Write b(n) for block(n), g(n) for generation(n), "
                + "F(n) for flattenedPrefix(n), and T(i) for fraction(i). Natural numbers include zero; "
                + "Occurs uses strictly positive generation and within-generation indices. T uses zero "
                + "for the first flattened entry. The source's one-based flattened position is flatIndex+1.")),
            Node("pairList", "The complete ordered pair list", PairFormula(),
                "flatMap visits x in list order, then map visits every y in that same list order. "
                + "Thus the numerator index is outermost and diagonal pairs are included. No final-generation restriction is imposed.",
                DescribeRole.Definition),
            Node("cumulative", "Cumulative lists and new suffixes", CumulativeFormula(),
                "freshTail(xs) is firstRetention of pairList(xs) filtered by absence from xs. "
                + "nextList(xs) is xs concatenated with this suffix. firstRetention scans from left to right, "
                + "keeping an entry exactly when its rational value has not already been seen. "
                + "The proof identifies that scan with Lean's eraseDups. Lean's last-retention dedup is not used.",
                DescribeRole.Definition),
            Node("generation", "Positive generation numbers", GenerationFormula(),
                "The empty generation zero is only an indexing convention and supplies no source positions. "
                + "The first block is the seed; subsequent blocks are precisely the newly appended suffixes.",
                DescribeRole.Definition),
            Node("flattenedPrefix", "Ordered finite flattening", FlattenFormula(),
                "range(n) lists 0 through n-1 in increasing order. flatMap concatenates the corresponding "
                + "generation blocks without reordering their entries.", DescribeRole.Definition),
            Node("Occurs", "Valid positive positions", OccursFormula(),
                "lookup is optional zero-based list lookup. The length bound and positive index exclude "
                + "default or out-of-range readings, including empty generations.", DescribeRole.Definition),
            Node("flatIndex", "The flattened index of a generation position", FlatIndexFormula(),
                "The length of F(n-1) counts all earlier entries; k-1 is the within-generation offset.",
                DescribeRole.Definition),
            Node("source_update", "Literal source update", UpdateFormula(),
                "For every duplicate-free old list, the prefix-plus-suffix construction equals "
                + "first-occurrence retention of the entire old list followed by the complete ordered pair list. "
                + "The old prefix remains in its original order.", DescribeRole.Theorem),
            Paragraph(Text("Strong induction on q simultaneously covers every p/q with 1<=p<=q. "
                + "The seed handles p=q. If p<q and 2p<=q, the permitted diagonal pair at p/(q-p) "
                + "produces p/q. If 2p>q, the pair (1,(q-p)/p) produces p/q. Both inputs are "
                + "moved into one common cumulative list by nesting. The canonical rational numerator "
                + "and positive denominator reduce an arbitrary interval rational to this induction. "
                + "Different generation blocks are disjoint because each new suffix excludes the entire old prefix. "
                + "Each block is duplicate-free, so uniqueness includes its within-generation index.")),
            Node("result", "The complete source event and array bridge", ResultFormula(),
                "The ten conjuncts below give the literal update, finite flattening, interval invariant, "
                + "exactly one positive generation/index pair for every target rational, unbounded prefixes, "
                + "consistent infinite readings, the position-to-flat bridge, a unique owner for every flat index, "
                + "injectivity of T, and its canonical reduced coordinates. num(i)=numerator(i)=(T(i)).num "
                + "and den(i)=denominator(i)=(T(i)).den. The arrays A371279 and A371280 are these two "
                + "coordinate records of the same T; neither coordinate is claimed individually injective. "
                + "This does not validate published finite array digits or execute Mathematica. "
                + "The denominator-induction candidate came from a GPT Pro search and was checked ordinarily "
                + "before this formalization; no independent-discovery or research-difficulty claim is made.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("kimberling-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Lists() => Call("List", Rat());
    private static Formula Pairs() => Seq(Nat(), Sp, Times, Sp, Nat());
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtN(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeN(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Cat(Formula a, Formula b) => Call("append", a, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
    private static Formula Conj(params Formula[] clauses) => Seq([.. clauses.SelectMany((c,i) => i == 0
        ? new Formula[] { Open, c, Close } : new Formula[] { Sp, Land, Sp, Open, c, Close })]);
    private static Formula For(Formula x, Formula type, Formula body) => Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(Formula x, Formula type, Formula body) => Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Unique(Formula x, Formula type, Formula body) => Seq(Exists, Sp, Bang, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Len(Formula x) => Call("length", x);
    private static Formula C(Formula n) => Call("C", n);
    private static Formula B(Formula n) => Call("b", n);
    private static Formula G(Formula n) => Call("g", n);
    private static Formula Flat(Formula n) => Call("F", n);
    private static Formula T(Formula n) => Call("T", n);
    private static Formula Lookup(Formula xs, Formula i) => Call("lookup", xs, i);
    private static Formula Some(Formula r) => Call("some", r);
    private static Formula Interval(Formula r) => Conj(LtN(D(0), r), LeN(r, D(1)));
    private static Formula PairFormula()
    {
        var xs=F.Id("s"); var x=F.Id("x"); var y=F.Id("y");
        return Disp(For(xs, Lists(), Eqn(Call("pairList",xs),
            Call("flatMap", Seq(x, Sp, Mapsto, Sp, Call("map", Seq(y, Sp, Mapsto, Sp,
                new Formula.Fraction(x,Add(D(1),y))),xs)),xs))));
    }
    private static Formula CumulativeFormula()
    {
        var n=F.Id("n");
        return Disp(Conj(Eqn(C(D(0)),Seq(OpenBracket,D(1),CloseBracket)),
            For(n,Nat(),Eqn(C(Add(n,D(1))),Call("nextList",C(n))))));
    }
    private static Formula GenerationFormula()
    {
        var n=F.Id("n");
        return Disp(Conj(Eqn(G(D(0)),Seq(OpenBracket,CloseBracket)),
            Eqn(B(D(0)),Seq(OpenBracket,D(1),CloseBracket)),
            For(n,Nat(),Conj(Eqn(G(Add(n,D(1))),B(n)),
                Eqn(B(Add(n,D(1))),Call("freshTail",C(n)))))));
    }
    private static Formula FlattenFormula()
    {
        var n=F.Id("n");
        return Disp(For(n,Nat(),Eqn(Flat(n),Call("flatMap",Named("b"),Call("range",n)))));
    }
    private static Formula OccursFormula()
    {
        var r=F.Id("r"); var n=F.Id("n"); var k=F.Id("k");
        return Disp(For(r,Rat(),For(n,Nat(),For(k,Nat(),
            Seq(Call("Occurs",r,Seq(Open,n,Comma,k,Close)),Sp,Iff,Sp,
                Conj(LtN(D(0),n),LtN(D(0),k),LeN(k,Len(G(n))),
                    Eqn(Lookup(G(n),Sub(k,D(1))),Some(r))))))));
    }
    private static Formula FlatIndexFormula()
    {
        var n=F.Id("n"); var k=F.Id("k");
        return Disp(For(n,Nat(),For(k,Nat(),Eqn(Call("flatIndex",Seq(Open,n,Comma,k,Close)),
            Add(Len(Flat(Sub(n,D(1)))),Sub(k,D(1)))))));
    }
    private static Formula UpdateFormula()
    {
        var xs=F.Id("s");
        return Disp(For(xs,Lists(),Imp(Call("Nodup",xs),Eqn(Call("nextList",xs),
            Call("eraseDups",Cat(xs,Call("pairList",xs)))))));
    }
    private static Formula ResultFormula()
    {
        var n=F.Id("n"); var i=F.Id("i"); var j=F.Id("j"); var r=F.Id("r"); var p=F.Id("p"); var t=F.Id("t");
        var update = For(n, Nat(), Eqn(C(Add(n,D(1))), Call("eraseDups", Cat(C(n), Call("pairList", C(n))))));
        var finite = For(n, Nat(), Eqn(C(n), Flat(Add(n,D(1)))));
        var invariant = For(n, Nat(), For(r, Rat(), Imp(Seq(r,Sp,InMacro,Sp,C(n)), Interval(r))));
        var complete = For(r, Rat(), Imp(Interval(r), Unique(p, Pairs(), Call("Occurs",r,p))));
        var unbounded = For(t, Nat(), Ex(n, Nat(), LtN(t, Len(Flat(n)))));
        var reading = For(n, Nat(), For(i, Nat(), Imp(LtN(i, Len(Flat(n))), Eqn(Lookup(Flat(n),i), Some(T(i))))));
        var positions = For(r, Rat(), For(p, Pairs(), Imp(Call("Occurs",r,p), Eqn(T(Call("flatIndex",p)),r))));
        var owners = For(t, Nat(), Unique(p, Pairs(), Conj(Call("Occurs",T(t),p), Eqn(Call("flatIndex",p),t))));
        var injective = For(i, Nat(), For(j, Nat(), Imp(Eqn(T(i),T(j)), Eqn(i,j))));
        var coordinates = For(i, Nat(), Conj(Interval(T(i)), LtN(D(0),Call("den",i)),
            Call("Coprime",Call("natAbs",Call("num",i)),Call("den",i)),
            Eqn(T(i),new Formula.Fraction(Call("num",i),Call("den",i)))));
        return Disp(Conj(update, finite, invariant, complete, unbounded, reading, positions, owners, injective, coordinates));
    }
}
