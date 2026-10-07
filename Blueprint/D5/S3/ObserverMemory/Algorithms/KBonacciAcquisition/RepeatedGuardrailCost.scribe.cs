using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class RepeatedGuardrailCostDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/RepeatedGuardrailCost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded INITIAL phase labels have exact paid repeated-query cost.",
        H("Exact cost of repeated guarded phase queries"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-repeated-guardrail-cost"),
            DeclarationHandle.Create(Owner + "original_repeated_guardrail_cost"),
            H("A guarded family of arbitrary initial labels"),
            StatementSource.FromAuthor(Disp(CostFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The codomain Y is arbitrary. The finite image of labels has n distinct elements. "
                    + "Write p=h*u+rho, T=g*p, k=T-1, and m=g*u. Coprimality gives gcd(m,T)=g, "
                    + "and m<T. The initial phase indexed by j is -j*g modulo T. "
                    + "The function f has the same prescribed label at every legal tail of each "
                    + "such phase in the fixed initial value fiber v. Its value at none is arbitrary, "
                    + "and the selector returns that value freely on initial rejection. No condition "
                    + "is imposed on other value fibers. The symbol positivek denotes the proof of "
                    + "0<k derived from the displayed parameter bounds.")),
                Paragraph(Text(
                    "The Boolean parameter a is localAlphabet. When it is true, the alphabet "
                    + "contains exactly the internally admissible Boolean words of length m; when "
                    + "it is false, every Boolean word of length m is available. Initial histories "
                    + "are finite lists of blocks from that alphabet, flattened and evaluated by "
                    + "the original scalar and scanner. A natural budget b is feasible when one "
                    + "selector emits words from the alphabet, returns f(none) on free initial "
                    + "rejection, and succeeds within b paid words for every such initial history "
                    + "whose endpoint output is some v. Success means returning f of that INITIAL "
                    + "record, with early stopping permitted. OriginalFiberCost is the infimum, "
                    + "in ENat, of all these feasible natural budgets; an empty set gives infinity.")),
                Paragraph(Text(
                    "Let A be the label at phase zero, R=clog(2,n)-1, and M=u-R*rho, with natural "
                    + "subtraction. Every phase with a label different from A lies at an index from "
                    + "1 through M. Choosing one index for each label, and index zero for A, injects "
                    + "the label image into 0 through M. Thus M>=n-1>=2. In particular R*rho<u, "
                    + "M+R*rho=u, and R*rho+2<=u; the guard is derived from the support condition.")),
                Paragraph(Text(
                    "For the lower bound choose actual complete-word initial histories with the "
                    + "same value and tail zero, one for each label. Throughout the first R*h paid "
                    + "blocks, every nonzero coefficient of these phases has block index divisible "
                    + "by h. On any shared chronological archive the current scalar and tail are "
                    + "common. A silent block preserves a common scalar endpoint. The scanner "
                    + "either accepts every candidate with a common new tail or rejects them all. "
                    + "An early stop or uniform absorbing rejection can identify only one label. "
                    + "An active block has at most two successful scalar endpoints. Induction on "
                    + "the actual execute function produces a binary transcript with at most R "
                    + "questions, counting every intervening paid word. Its leaves number at most "
                    + "2^R, whereas n>2^R. Every feasible finite budget is therefore at least R*h+1.")),
                Paragraph(Text(
                    "For the upper bound assign distinct R+1 bit codes to the initial labels, "
                    + "with the code of A equal to zero. At paid block index ell*h, for ell from "
                    + "0 through R, place a pulse at local position (j+ell*rho)*g-1 exactly when "
                    + "the ell-th bit of label j is one. Every other position is zero. The guard "
                    + "places each pulse in the complete word. Its absolute position is ell*T+j*g-1, "
                    + "so the scalar endpoint difference reads exactly that INITIAL code bit. "
                    + "The word starts with zero, its pulses are separated by at least g, and its "
                    + "terminal tail is at most one. The same word is internally admissible and "
                    + "safe from every legal old tail. Between query words issue h-1 complete zero "
                    + "words. All padding and waiting words are paid and recorded.")),
                Paragraph(Text(
                    "The selector receives the free initial value and the chronological archive "
                    + "of complete issued words with their endpoint outputs. It chooses the next "
                    + "word from the archive length. After R*h+1 words it matches the archive to "
                    + "the unique initial label code. Differences of successive query endpoints "
                    + "recover every coordinate of that code. The result is the label of the "
                    + "INITIAL record throughout the execution. The construction works in both "
                    + "complete-word alphabets, with all actual initial histories and tails in scope. "
                    + "The infimum in ENat includes possible infinite costs; this family has the "
                    + "displayed finite cost. The proof also includes h=1 and R=1."))),
            DescribeRole.Theorem))));

    private static Formula CostFormula()
    {
        var Y = F.Id("Y"); var g = F.Id("g"); var u = F.Id("u"); var h = F.Id("h");
        var rho = F.Id("rho"); var p = F.Id("p"); var k = F.Id("k"); var m = F.Id("m");
        var labels = F.Id("labels"); var n = F.Id("n"); var R = F.Id("R"); var M = F.Id("M");
        var A = F.Id("A"); var f = F.Id("f"); var v = F.Id("v"); var a = F.Id("a");
        var j = F.Id("j"); var s = F.Id("s"); var T = Add(k, D(1));
        var parameters = And(Rel(D(2), Leq, g), Rel(D(2), Leq, u), Rel(D(1), Leq, h),
            Rel(D(1), Leq, rho), Rel(rho, Lt, u), Call("Coprime", u, rho));
        var support = All(j, Call("Fin", p), Imp(NotEqual(App(labels, j), A),
            And(Rel(D(1), Leq, Call("val", j)), Rel(Call("val", j), Leq, M))));
        var phase = Seq(Minus, Call("cast", Multiply(Call("val", j), g), Call("ZMod", T)));
        var restriction = All(j, Call("Fin", p), All(s, NatType(), Imp(Rel(s, Lt, k),
            Equal(App(f, Call("some", Triple(v, phase, s))), App(labels, j)))));
        var equality = Equal(Call("OriginalFiberCost", k, m, Op("positivek"), a, f, v),
            Call("cast", Add(Multiply(R, h), D(1)), Op("ENat")));
        var target = All(f, Rel(Call("Option", Call("LiveRecord", k)), To, Y),
            All(v, Call("ZMod", D(2)), All(a, Op("Bool"),
                Imp(And(Rel(D(3), Leq, n), support, restriction), equality))));
        var body = Let(p, Add(Multiply(h, u), rho), Let(k, Call("natSub", Multiply(g, p), D(1)),
            Let(m, Multiply(g, u), All(labels, Rel(Call("Fin", p), To, Y),
                Let(n, Call("card", Call("range", labels)),
                    Let(R, Call("natSub", Call("clog", D(2), n), D(1)),
                        Let(M, Call("natSub", u, Multiply(R, rho)),
                            Let(A, App(labels, D(0)), target))))))));
        return All(Y, Op("Type"), All(g, NatType(), All(u, NatType(), All(h, NatType(),
            All(rho, NatType(), Imp(parameters, body))))));
    }

    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Triple(Formula a, Formula b, Formula c) => Seq(Open, a, Comma, b, Comma, c, Close);
    private static Formula Rel(Formula a, Formula relation, Formula b) => Seq(a, Sp, relation, Sp, b);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Imp(Formula a, Formula b) => Par(Rel(Par(a), Implies, Par(b)));
    private static Formula All(Formula w, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, Open, w, Colon, type, Close, Comma, Sp, Par(body)));
    private static Formula Let(Formula w, Formula value, Formula body) =>
        Seq(Op("let"), Sp, w, Eq, value, Sp, Op("in"), Sp, Par(body));
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.Add(Seq(Sp, Land, Sp));
            items.Add(clauses[index]);
        }
        return Par(Seq([.. items]));
    }
}
