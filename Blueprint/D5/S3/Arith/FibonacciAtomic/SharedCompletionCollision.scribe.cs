using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SharedCompletionCollisionDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula ImpliesOf(Formula a, Formula b) => Par(Seq(a, Sp, Implies, Sp, b));
    private static Formula IffOf(Formula a, Formula b) => Par(Seq(a, Sp, Iff, Sp, b));
    private static Formula All(string names, Formula body)
    {
        var vars = names switch
        {
            "uv" => Seq(V("u"),Comma,V("v"),InMacro,Call("Word",V("k"))),
            "ccprime" => Seq(V("c"),Comma,V("cprime"),InMacro,Call("Side",V("k"),V("A"))),
            "ihst" => Seq(Par(Seq(V("i"),Colon,Call("Fin",Seq(V("k"),Plus,D(1))))),
                Par(Seq(V("h"),Colon,V("i"),InMacro,Sp,V("A"))),
                Par(Seq(V("s"),Comma,V("t"),Colon,Call("State")))),
            "is" => Seq(Par(Seq(V("i"),Colon,Call("Fin",Seq(V("k"),Plus,D(1))))),
                Par(Seq(V("s"),Colon,Call("State")))),
            "it" => Seq(Par(Seq(V("i"),Colon,Call("Fin",Seq(V("k"),Plus,D(1))))),
                Par(Seq(V("t"),Colon,Call("State")))),
            "i" => Seq(V("i"),InMacro,Call("Fin",Seq(V("k"),Plus,D(1)))),
            "t" => Seq(V("t"),InMacro,Call("State")),
            _ => throw new System.ArgumentOutOfRangeException(nameof(names))
        };
        return Par(Seq(Forall, Sp, vars, Comma, Sp, Par(body)));
    }
    private static Formula K(Formula q) => Call("matrixEntry", q);
    private static Formula Ind(Formula p) => Call("indicator", p);
    private static Formula Prob(string name, params Formula[] args) => Call(name, args);
    private static Formula Const(string c) => Call("constantWord", Call(c));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shared raw complement collision law equals the ordered six-state scalar transfer "
        + "entry.",
        H("Shared Completion and First Rejection"),
        Blocks(
            Paragraph(Text("Let k be any natural number and n=k+1. A is any subset of Fin(n), "
                + "B is its complementary subtype, and P,Q are any reachable profiles in "
                + "Profile(k,A). "
                + "The arbitrary actual assignments a,a' on A satisfy code(A,a)=encode(P) and "
                + "code(A,a')=encode(Q). No canonical-choice restriction is imposed on them. "
                + "The alphabet consists of all five complete windows 000,100,010,101,001, written "
                + "from low to high; all raw assignments remain in the domain, including bad "
                + "seams, "
                + "terminal zero, and every suffix after rejection. Zero consumes one position.")),
            Paragraph(Text("T means the original frozen task: the earliest bad seam, then terminal "
                + "zero if every seam passed, then acceptance. A Lean finite label j represents "
                + "source "
                + "label j+1, and top represents acceptance. A merged word uses a on A and b on B. "
                + "G(a,a')=sharedProbability is the sum of the indicators T(merge(A,a,b))="
                + "T(merge(A,a',b)), over every b:B->Window, divided by 5^|B|. "
                + "U(a,a')=fullProbability uses the same event after fullMerge, summing over all "
                + "n-coordinate raw words and dividing by 5^n. Its A coordinates are dummy draws. "
                + "Gamma(P,Q)=collisionProbability is U for the frozen canonical representatives. "
                + "independentCollision(k,A,a,a') instead sums the collision indicators over two "
                + "independent full dummy words u,v and divides by 5^(2n). "
                + "Every B coordinate supplies the SAME whole window to both histories; distinct "
                + "coordinates are independent. No independence of bits inside a window is "
                + "asserted.")),
            Paragraph(Text("The six states are s00,s01,s10,s11,E,D in that order. The initial "
                + "state is s00. Each live state stores the two previous high bits. On symbols "
                + "c,d, "
                + "step first tests the incoming seams r AND first(c), r' AND first(d). Both "
                + "failures "
                + "give E; one gives D; neither installs the actual high-bit pair at a nonterminal "
                + "position. At the terminal position, neither failure gives E precisely when "
                + "the two current zero-window flags agree, and gives D otherwise. E and D absorb. "
                + "End is the external query already folded into this terminal operator; there is "
                + "no extra symbol, input position, or random draw.")),
            Paragraph(Text("Qa=actualMatrix(k,A,a,a') is the position-dependent matrix. At i it "
                + "averages, with weight 1/5, the one-hot transitions step(i=last(k),s,c,d) over "
                + "the five x, where c=a(i),d=a'(i) on A and c=d=x on B. Qc=SharedMatrix(k,A,P,Q) "
                + "uses the canonical representatives. K(Q)=matrixEntry(Q) is the s00,E entry "
                + "of the chronological product List.ofFn(Q).prod. I is the rational equality "
                + "indicator, one when its argument holds and zero otherwise. terminal(i) is the "
                + "Boolean test i=last(k). terminalOrNonterminal(i) "
                + "means terminalMatrix when i=last(k), and nonterminalMatrix otherwise. "
                + "constantWord denotes the singleton word on Fin(1).")),
            Describe.Lean(DescribeId.Create("shared-completion-collision"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/SharedCompletionCollision.result"),
                H("Complete Shared Collision Law"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The statement below is one conjunction under all its displayed "
                        + "binders and representative equations. u,v range over all Word(k); c,c' "
                        + "range over Side(k,A); i ranges over Fin(k+1); s,t range over the six "
                        + "states. "
                        + "Qa(c,c') denotes actualMatrix with those assignments. In the "
                        + "fixed-position "
                        + "clause the assignments are evaluated on the subtype element (i,h), for "
                        + "the "
                        + "given h:i in A. The full-cut indicator uses extend(A,a), which equals "
                        + "the "
                        + "deterministic full word when A is all coordinates.")),
                    Paragraph(Text("For the actual nonterminal prefix of m positions, search the "
                        + "incoming-seam tests with findIdx?. Every stored first hit r satisfies "
                        + "r<m. "
                        + "Two absent hits give the live previous-bit state; two equal finite hits "
                        + "give E; all other cases give D. A new first hit at m cannot equal an "
                        + "old "
                        + "r<m. At m=k this same bound separates earlier stops from the last "
                        + "incoming "
                        + "seam and terminal zero. The full test list is false followed by the "
                        + "original bad tests; its first hit is the injective encoding top->none, "
                        + "j->some(j+1) of T. Thus the run event is exactly the original task "
                        + "equality.")),
                    Paragraph(Text("Reindexing the finite raw assignment sums yields the ordered "
                        + "matrix recurrence. The dummy A-coordinate fibers have multiplicity "
                        + "5^|A|, "
                        + "which cancels from 5^n to give the B-only law. At an A position, five "
                        + "identical dummy summands cancel to the deterministic one-hot operator. "
                        + "The absorbing rows sum to one, so every raw suffix retains its full "
                        + "mass. "
                        + "The frozen response-fiber theorem transports labels for each fixed b, "
                        + "establishing independence of the scalar entry from representative "
                        + "choice. "
                        + "Individual factors and the full product matrix need not be independent "
                        + "of that choice.")),
                    Paragraph(Text("The nonterminal and terminal B operators are the following "
                        + "exact matrices. The terminal rows from s00,s11 put mass one at E; those "
                        + "from s01,s10 put 3/5 at E and 2/5 at D. Both absorbers self-loop.")),
                    new DocumentBlock.DisplayFormula(MatrixFormula("nonterminalMatrix", [
                        [3,0,0,2,0,0], [2,0,0,1,0,2], [2,0,0,1,0,2],
                        [2,0,0,1,2,0], [0,0,0,0,5,0], [0,0,0,0,0,5]])),
                    new DocumentBlock.DisplayFormula(MatrixFormula("terminalMatrix", [
                        [0,0,0,0,5,0], [0,0,0,0,3,2], [0,0,0,0,3,2],
                        [0,0,0,0,5,0], [0,0,0,0,5,0], [0,0,0,0,0,5]])),
                    Paragraph(Text("At n=1 and A empty, sharing the complement gives collision "
                        + "one; two independent completions give 17/25. Zero and middle have the "
                        + "same ports and nonterminal transition, but their terminal labels "
                        + "differ. "
                        + "This is a position-scheduled evaluator with externally supplied cut and "
                        + "representatives. It asserts neither minimal state count nor an "
                        + "autonomous "
                        + "clock, and uses no rank premise."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var k = V("k"); var a = V("a"); var ap = V("aprime"); var p = V("P"); var q = V("Q");
        var cut = V("A"); var qa = V("Qa"); var qc = V("Qc"); var u = V("u"); var v = V("v");
        var c = V("c"); var cp = V("cprime"); var i = V("i"); var s = V("s"); var t = V("t");
        var e = V("E"); var diff = V("D");
        Formula Task(Formula w) => Call("T", w);
        Formula G(Formula x, Formula y) => Prob("G", x, y);
        Formula Gamma(Formula x, Formula y) => Prob("Gamma", x, y);
        Formula Run(Formula x, Formula y) => Call("pairRunWord", x, y);
        Formula Code(Formula x, Formula y) => EqOf(Call("code", cut, x), Call("encode", y));
        Formula EmptyGamma() => Call("collisionProbability", D(0), Emptyset,
            Call("emptyProfile0"), Call("emptyProfile0"));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, k, Sp, InMacro, Sp, Call("Nat"), Comma, Sp,
                Forall, Sp, cut, Sp, Subseteq, Sp, Call("Fin", Seq(k, Plus, D(1))), Comma),
            Seq(Forall, Sp, p, Comma, q, Sp, InMacro, Sp, Call("Profile", k, cut), Comma,
                Sp, Forall, Sp, a, Comma, ap, Sp, InMacro, Sp, Call("Side", k, cut), Comma),
            Seq(Forall,Sp,Par(Seq(V("ha"),Colon,Code(a,p))),Comma,Sp,
                Forall,Sp,Par(Seq(V("haprime"),Colon,Code(ap,q))),Comma),
            Seq(Open,All("uv", And(IffOf(EqOf(Run(u,v),e), EqOf(Task(u),Task(v))),
                And(IffOf(EqOf(Run(u,v),diff),Seq(Task(u),Neq,Task(v))),
                    Par(Seq(EqOf(Run(u,v),e),Sp,Lor,Sp,EqOf(Run(u,v),diff))))))),
            Seq(Land, Sp, EqOf(Call("U",a,ap),G(a,ap)), Sp, Land, Sp, EqOf(G(a,ap),K(qa))),
            Seq(Land, Sp, EqOf(G(a,ap),Gamma(p,q)), Sp, Land, Sp, EqOf(K(qa),K(qc)),
                Sp, Land, Sp, EqOf(Gamma(p,q),K(qc))),
            Seq(Land, Sp, All("ccprime",ImpliesOf(And(Code(c,p),Code(cp,q)),
                EqOf(K(Call("Qa",c,cp)),K(qa))))),
            Seq(Land, Sp, All("ihst",
                EqOf(Call("Qa",i,s,t),Ind(EqOf(Call("step",Call("terminal",i),s,
                    Call("a",i,V("h")),Call("aprime",i,V("h"))),t))))),
            Seq(Land, Sp, All("i",ImpliesOf(Seq(Neg,Sp,i,InMacro,Sp,cut),
                EqOf(Call("Qa",i),Call("terminalOrNonterminal",i))))),
            Seq(Land, Sp, All("is",And(All("t",Seq(D(0),Le,Call("Qa",i,s,t))),
                EqOf(Seq(new Formula.Subscript(Sum,t),Call("Qa",i,s,t)),D(1))))),
            Seq(Land, Sp, All("it",And(EqOf(Call("Qa",i,e,t),Ind(EqOf(e,t))),
                EqOf(Call("Qa",i,diff,t),Ind(EqOf(diff,t)))))),
            Seq(Land, Sp, EqOf(Gamma(p,p),D(1))),
            Seq(Land, Sp, All("ccprime",ImpliesOf(And(Code(c,p),Code(cp,p)),EqOf(G(c,cp),D(1))))),
            Seq(Land, Sp, ImpliesOf(EqOf(cut,Emptyset),EqOf(Gamma(p,q),D(1)))),
            Seq(Land, Sp, ImpliesOf(EqOf(cut,Call("univ")),EqOf(G(a,ap),
                Ind(EqOf(Task(Call("extend",cut,a)),Task(Call("extend",cut,ap))))))),
            Seq(Land, Sp, EqOf(EmptyGamma(),D(1)), Sp, Land, Sp,
                EqOf(Call("independentCollision",D(0),Emptyset,
                    Call("emptySide0"),Call("emptySide0")),
                    new Formula.Fraction(D(1,7),D(2,5)))),
            Seq(Land, Sp,
                EqOf(Call("step",Call("true"),Call("s00"),Call("zero"),Call("middle")),diff),
                Sp, Land, Sp,
                EqOf(Call("step",Call("false"),Call("s00"),Call("zero"),Call("middle")),
                    Call("s00"))),
            Seq(Land, Sp, EqOf(Task(Const("zero")),Call("finiteLabel",D(0))), Sp, Land, Sp,
                EqOf(Task(Const("middle")),Call("top")),Close)
        ]));
    }

    private static Formula MatrixFormula(string name, int[][] entries)
    {
        var body = new System.Collections.Generic.List<Formula>();
        for (var r = 0; r < entries.Length; r++)
        {
            if (r > 0) body.Add(RowBreak);
            for (var c = 0; c < entries[r].Length; c++)
            {
                if (c > 0) body.Add(Amp);
                body.Add(new Formula.Number(entries[r][c]));
            }
        }
        return Disp(EqOf(Call(name), Seq(new Formula.Fraction(D(1),D(5)),
            Begin, Grp(V("bmatrix")), Seq([.. body]), End, Grp(V("bmatrix")))));
    }
}
