using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciIntervalBlockCouplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact exterior-conditioned coupling on either side of a single disagreement.",
        H("Interval assignments and their uniform conditional laws"),
        Blocks(
            Paragraph(Text(
                "Let W(n) be Fin n to Bool, and let A(k,n,w) mean DBonacciAdmissible. "
                + "For a finite set B of sites, Assign(B) is the type of Boolean functions "
                + "on the subtype of sites belonging to B. Restricting a full word w to "
                + "that subtype gives restrictBlock(B,w). The law L(k,B,x,h) is "
                + "conditionalBlockLaw: the pushforward to Assign(B) of the uniform "
                + "law on legal full words agreeing with x at every site in the full "
                + "complement of B. Here h certifies legality of x and hence nonemptiness. "
                + "Two completions with the same restriction agree inside B and at all "
                + "exterior sites, so restriction is injective on that fiber. Thus this "
                + "pushforward is the uniform law on legal B assignments with that exterior.")),
            Paragraph(Text(
                "H(B,p) denotes blockHamming, the sum over sites i in B of the indicator "
                + "that the two assignments p.first(i) and p.second(i) differ. "
                + "E(J,H(B)) denotes the ENNReal sum over assignment pairs p of J(p)H(B,p). "
                + "All sites of the exterior are retained, including both ends of the interval.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-conditional-interval-block-coupling"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciIntervalBlockCoupling.conditional_interval_block_coupling"),
                H("An actual joint law with exact block marginals and cost at most one"),
                StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Put B=Icc(a,b). The assumption a at most b makes B nonempty; it may "
                    + "touch either endpoint of the word or have length smaller than k. "
                    + "Since u is outside this interval, either u is before every site "
                    + "of B or after every site of B. In the first case sort B increasingly "
                    + "and apply the conditional recursive scan. Its full-word projections "
                    + "are the exact completion laws and its expected internal Hamming "
                    + "cost is at most one. In the second case reverse all coordinates "
                    + "by Fin.rev. The existing forbidden-window reversal theorem proves "
                    + "legality is preserved. Reversal is an involutive bijection between "
                    + "the actual fixed-coordinate completion fibers, so it transports "
                    + "their uniform PMFs exactly. Apply the increasing scan to the "
                    + "reflected block, reverse both sampled full words back, and then "
                    + "restrict to B. The same site bijection preserves the Hamming sum. "
                    + "Composition of PMF maps proves both displayed marginal equalities. "
                    + "The proof uses the direct expected-cost estimate; it makes no "
                    + "claim about an explicit geometric survival-event tail."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var x = F.Id("x"); var y = F.Id("y");
        var a = F.Id("a"); var b = F.Id("b"); var u = F.Id("u"); var i = F.Id("i");
        var h = F.Id("h"); var g = F.Id("g"); var j = F.Id("J");
        var block = Call("Icc", a, b);
        var same = All(i, Call("Fin", n), Imp(Rel(i, Neq, u),
            Rel(Call("at", x, i), Eq, Call("at", y, i))));
        var laws = And(Rel(Call("mapFst", j), Eq, Call("L", k, block, x, h)),
            Rel(Call("mapSnd", j), Eq, Call("L", k, block, y, g)),
            Rel(Call("E", j, Call("H", block)), Leq, D(1)));
        var pairType = Seq(Call("Assign", block), Sp, Times, Sp, Call("Assign", block));
        var joint = Par(Seq(Exists, Sp, Open, j, Colon, Call("PMF", pairType), Close,
            Comma, Sp, laws));
        var outside = Seq(Neg, Sp, Par(Seq(u, Sp, InMacro, Sp, block)));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(2), Leq, k),
            All(Seq(x, Comma, y), Word(n), All(h, Call("A", k, n, x),
                All(g, Call("A", k, n, y), All(Seq(a, Comma, b, Comma, u), Call("Fin", n),
                    Imp(And(Rel(a, Leq, b), outside, same), joint)))))));
    }

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Word(Formula n) => Seq(Open, Call("Fin", n), Sp, To, Sp, Op("Bool"), Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Rel(Formula a, Formula r, Formula b) => Seq(a, Sp, r, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(Formula v, Formula t, Formula body) => Par(Seq(Forall, Sp, Open, v, Colon, t, Close, Comma, Sp, Par(body)));
    private static Formula Imp(Formula a, Formula b) => Par(Rel(Par(a), Implies, Par(b)));
    private static Formula And(params Formula[] parts)
    {
        var result = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < parts.Length; ++i)
        {
            if (i > 0) result.Add(Seq(Sp, Land, Sp));
            result.Add(Par(parts[i]));
        }
        return Par(Seq([.. result]));
    }
}
