using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSimultaneousPrefixSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSimultaneousPrefixSeparation", H("Simultaneous finite prefix separation"), Blocks(
            Describe.Lean(DescribeId.Create("native-simultaneous-prefix-separation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeSimultaneousPrefixSeparation.simultaneous_prefix_separation"),
                H("Independent live patterns preserve a finite conjunction"), Statement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The input fixes an arbitrary rank vector n, finite coordinates f, an arbitrary rank policy P, and a finite list of decorated mixed expression pairs. The original residual domain is split into the fixed Fin r coordinates and the remaining Fin m coordinates by the executable sum equivalence. FixedExpr evaluates the fixed coordinates into grounds while retaining each live residual name and every native decoration. The policy P(n) is identical on both sides.")),
                    Paragraph(Text("Each live original coordinate has its own depth and native pattern. A depth-zero pattern is one hole; a positive-depth leaf is that actual leaf and has no holes below it; a pair keeps the two ordered child patterns. HoleCount and HoleEquiv count and number these reached holes recursively, left before right. HoleNumbering combines the independent coordinate frontiers with the executable finSigmaFinEquiv. No choice of an equivalence from a finite type is used to compute the tuple.")),
                    Paragraph(Text("PatternExpr replaces each reached hole by its own zero-decorated name. Repeated uses of an original residual always reuse that same pattern and the same hole names. Shift pushes the actual native substitution through a context, using the native pair homomorphism and addition of iterate exponents. Bind then satisfies the exact substitution/evaluation bridge. Expanded applies this bridge after fixing n and f, and ExpandedList preserves every listed occurrence.")),
                    Paragraph(Text("If one expanded equality were universal on the entire independent hole product, the existing prefix identity reflection would make the original equality universal on every live residual valuation. This contradicts the supplied finite witness. Uniform residual realization is applied once to the entire expanded list, giving one common hole tuple. PrefixTuple fills each supplied pattern with its assigned coordinates of this same tuple. The exact depth decomposition returns each original pattern, including every early leaf and its absent descendants.")),
                    Paragraph(Text("This proves the finite live-pattern construction. Its conclusion preserves the supplied patterns and all listed disequalities at the fixed arbitrary n and f, including zero dimensions and the empty list. The correspondence from an actual infinite completion tree and its finite inclusive reply prefix through depth h to a live Pattern(h+1), preserving early terminal children and absent regions, is not supplied by this theorem. That correspondence remains necessary for the full completion-tree formulation of Signed Local Prefix Lifting Lemma 2.1. A renamed live-pattern assumption does not discharge it.")),
                    Paragraph(Text("The result concerns exact native whole-tree equalities and independent Cartesian hole fillings. It provides no acquisition, resource bound, arithmetic elimination, support closure or full Functional Joint Contact theorem. Unknown audit continuation does not assert emptiness or undecidability."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource Statement()
    {
        var coord = Call("Fin",V("m"));
        var rank = Arr(Call("Fin",V("k")),V("Nat"));
        var expr = Call("RankedExpr",V("k"),Seq(V("r"),Sp,Plus,Sp,V("m")));
        var pair = Call("Prod",expr,expr);
        var patterns = Dep("i",coord,Call("Pattern",Call("d",V("i"))));
        var tuple = Call("prefixTuple",V("n"),V("f"),V("d"),V("p"),V("L"));
        Formula Negatives(Formula z) => All("e",pair,Imp(Mem(V("e"),V("L")),
            NeOf(Call("fixedEval",V("n"),V("f"),z,Call("fst",V("e"))),
                Call("fixedEval",V("n"),V("f"),z,Call("snd",V("e"))))));
        var premise = Some("z",Arr(coord,V("Source")),AndOf(Call("P",V("n")),Negatives(V("z"))));
        var preserved = All("i",coord,EqOf(Call("fst",Call("decompose",Call("d",V("i")),Call("prefixTuple",V("n"),V("f"),V("d"),V("p"),V("L"),V("i")))),Call("p",V("i"))));
        var conclusion = AndOf(Call("P",V("n")),AndOf(preserved,Negatives(tuple)));
        return StatementSource.FromAuthor(Disp(All("k,r,m",V("Nat"),All("L",Call("List",pair),
            All("P",Arr(Par(rank),V("Prop")),All("n",rank,All("f",Arr(Call("Fin",V("r")),V("Source")),
            All("d",Arr(coord,V("Nat")),All("p",patterns,
            Imp(All("i",coord,Call("Nonempty",Call("Frontier",Call("p",V("i"))))),IffOf(premise,conclusion)))))))))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula AndOf(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Dep(string n, Formula t, Formula b) => Arr(Par(Seq(V(n), Colon, Sp, t)), b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
