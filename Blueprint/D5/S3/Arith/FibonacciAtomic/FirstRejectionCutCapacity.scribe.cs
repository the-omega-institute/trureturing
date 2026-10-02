using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FirstRejectionCutCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Cap(Formula a) => Call("capacityT", a);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coordinate cut has an exact first-rejection response count and an exact Boolean collapse.",
        H("First Rejection Across Arbitrary Window Cuts"),
        Blocks(
            Paragraph(Text("Let n=k+1 for an arbitrary natural k. Coordinates are the complete windows "
                + "000,100,010,101,001, written from low to high. Inputs include every word of length n, "
                + "with arbitrary seams and terminal zero windows. The initial state has both flags false, "
                + "and End is queried after the last window. A is any subset of the coordinates; its "
                + "complementary assignments range over all five-window words on the other coordinates.")),
            Paragraph(Text("Ordered diagnostic. T is the earliest bad seam, where the left high bit and right low bit are both one. If no seam fails, T is the terminal label n for a last window 000, and is acceptance otherwise. The Lean label is WithTop(Fin(n)): finite value i represents source label i+1, and top represents acceptance. F is the Boolean End readout of the actual run from (false,false).")),
            Paragraph(Text("Crossing and closed seams. C consists of seams with exactly one endpoint in A; J consists of seams with both endpoints in A. The number d is the cardinality of C. For j in J, c(j) counts crossing seams strictly before j. A crossing port is the left high bit when the left coordinate lies in A, and the right low bit otherwise. The value delta is one exactly when n>=2, the terminal coordinate lies in A, and its predecessor does not. The factor terminalOwned(A) is the numeric indicator of terminal ownership.")),
            Paragraph(Text("Independent permitted profiles. Extend an A assignment by middle windows outside A. Its diagnostic tau is the first A-closed seam failure or the A-owned terminal zero failure. A profile consists of an allowed cutoff and the crossing bits strictly before it. The allowed cutoffs are acceptance, each seam in J, and the terminal label when n lies in A. Only for a terminal cutoff is the incoming last crossing port fixed to zero. There are no other restrictions.")),
            Paragraph(Text("For natural endpoints l<r<=n, I(l,r) is the half-open coordinate "
                + "interval [l,r), with zero-based coordinates l through r-1. terminal(n) denotes "
                + "coordinate n-1. leftCut(l) is zero at l=0 and one otherwise; rightCut(r) is "
                + "zero at r=n and one otherwise. singletonSuffix(l,r) is one exactly when "
                + "0<l, r=n, and r-l=1, and is zero otherwise. Subtractions below are natural "
                + "subtractions.")),
            Describe.Lean(DescribeId.Create("interval-cut-data"),
                DeclarationHandle.Create(Prefix + "interval_data"), H("Interval Seams and Terminal Ownership"),
                StatementSource.FromAuthor(IntervalDataFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The only crossing seams are the two interval boundaries "
                    + "that do not coincide with the ends of the whole word. The internal seams "
                    + "are the r-l-1 consecutive pairs inside the interval, and every such seam "
                    + "has exactly leftCut(l) earlier crossings. The terminal coordinate belongs "
                    + "to the interval exactly when r=n. The terminal incoming-port correction "
                    + "is nonzero exactly for a terminal singleton with a nonempty left complement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("first-rejection-cut-capacity"),
                DeclarationHandle.Create(Prefix + "result"), H("All Cuts, All Positive Lengths"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every permitted profile has an actual representative. At each coordinate, "
                        + "choose the low and high bits independently: middle, low, high, and ends encode "
                        + "the four possible bit pairs. Set the specified crossing bits, keep internal seams "
                        + "harmless before the selected cutoff, and put high followed by low at a selected "
                        + "internal failure. A terminal profile uses zero at the last coordinate. Its fixed "
                        + "incoming zero makes this compatible with the remaining prescribed bits. Representatives "
                        + "on opposite sides occupy disjoint coordinates and combine into one actual raw word.")),
                    Paragraph(Text("Two assignments have the same diagnostic response exactly when their "
                        + "cutoffs and preceding crossing bits agree. A complementary assignment of middle "
                        + "windows exposes the cutoff. A single low or high complementary window tests a "
                        + "selected crossing port and has its other bit zero. It therefore distinguishes "
                        + "different preceding ports while creating no earlier complementary failure. The "
                        + "empty complement has its unique assignment and still distinguishes closed labels.")),
                    Paragraph(Text("The actual response range is consequently in bijection with the independent "
                        + "profile family. Acceptance contributes 2^d profiles; an internal cutoff j contributes "
                        + "2^c(j); the terminal cutoff contributes 2^(d-delta). The incoming restriction removes "
                        + "exactly one available bit when delta=1, and delta<=d.")),
                    Paragraph(Text("The interval table is complete: the empty cut has capacity 1; the full cut "
                        + "has n+1; the proper prefix [1,m] has m+1; the terminal singleton has 3 for n>=2; "
                        + "a terminal suffix [l,n] with 1<l<n has 2(n-l+1)+2; and an interior interval [l,r] "
                        + "with 1<l<=r<n has 2(r-l+1)+2. Thus the first singleton has 2, an interior singleton "
                        + "has 4, and every nonprefix interval of length at least two has 2m+2. At n=1 the "
                        + "empty and full cuts have 1 and 2. There is no length-zero coordinate domain here.")),
                    Paragraph(Text("Projection sends acceptance to true and every finite label to false, "
                        + "and equals the actual Boolean End readout. Every assignment with a finite closed "
                        + "cutoff has the same zero Boolean response. Assignments with an acceptance cutoff "
                        + "have nonzero responses and remain distinguishable exactly by their full crossing "
                        + "profiles. The extra zero response exists precisely when A owns the terminal "
                        + "coordinate or has an internal seam. Writing epsilon for that condition gives "
                        + "Boolean capacity 2^d+epsilon.")),
                    Paragraph(Text("For every n>=2, the words x=(001,100,010^(n-2)) and "
                        + "y=(010^(n-1),000) both have Boolean output false. Their diagnostic outputs are "
                        + "the first seam label 1 and the terminal label n, respectively. Hence no function "
                        + "of the Boolean output alone reconstructs the diagnostic on all raw inputs. This "
                        + "does not restrict computation from the full raw word."))), DescribeRole.Theorem))));

    private static Formula IntervalDataFormula()
    {
        var l = V("l"); var r = V("r"); var n = V("n"); var j = V("j");
        var interval = Call("I", l, r); var left = Call("leftCut", l);
        return Seq(Forall, Sp, l, Comma, Sp, Forall, Sp, r, Comma, Sp,
            l, Sp, Lt, Sp, r, Sp, Land, Sp, r, Sp, Le, Sp, n, Sp, Implies, Sp, Grp(Seq(
                EqOf(Call("d", interval), Add(left, Call("rightCut", r))), Sp, Land, Sp,
                EqOf(Call("card", Call("J", interval)), Sub(Sub(r, l), D(1))), Sp, Land, Sp,
                Grp(Seq(Forall, Sp, j, Sp, InMacro, Sp, Call("J", interval), Comma, Sp,
                    EqOf(Call("c", interval, j), left))), Sp, Land, Sp,
                Grp(Seq(Call("terminal", n), Sp, InMacro, Sp, interval, Sp, Iff, Sp, r, Sp, Eq, Sp, n)),
                Sp, Land, Sp, EqOf(Call("delta", interval), Call("singletonSuffix", l, r)))));
    }

    private static Formula ResultFormula()
    {
        var n = V("n"); var a = V("A"); var d = V("d"); var c = V("c");
        var delta = DeltaLower; var eps = V("epsilon"); var j = V("j");
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(j, Sp, InMacro, Sp, V("J"))),
            Pow(D(2), Call("c", j)));
        Formula terminal = Seq(Call("terminalOwned", a), Sp, Times, Pow(D(2), Sub(d, delta)));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Sp, Ge, Sp, D(1), Comma, Sp, Forall, Sp, a, Sp, Subseteq, Sp,
                Call("coordinates", n), Comma),
            EqOf(Cap(a), Add(Add(Pow(D(2), d), sum), terminal)),
            Seq(delta, Sp, Le, Sp, d, Comma, Sp, EqOf(Call("project", V("T")), V("F"))),
            EqOf(Call("capacityF", a), Add(Pow(D(2), d), eps)),
            Seq(Forall, Sp, n, Sp, Ge, Sp, D(2), Comma, Sp,
                EqOf(Call("F", Call("x", n)), D(0)), Comma, Sp,
                EqOf(Call("F", Call("y", n)), D(0))),
            Seq(EqOf(Call("T", Call("x", n)), D(1)), Comma, Sp,
                EqOf(Call("T", Call("y", n)), n))
        ]));
    }
}
