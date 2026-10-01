using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ScalarPrefixAcquisitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered digit protocol identifies a prime-power residue with at most "
            + "e(p-1) complete valuation queries and retains its decoded value at termination.",
        H("Ordered prefix acquisition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-ordered-prefix-acquisition"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/ScalarPrefixAcquisition.scalar_prefix_acquisition"),
                H("The exact digit loop preserves its prefix and query budget"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be prime, e be positive, and X=ZMod(p^e). The complete readout "
                            + "q(c,y) is the greatest j at most e such that y and c are "
                            + "congruent modulo p^j. Testing center c therefore returns the "
                            + "capped valuation of y-c; equivalently it tests the shift -c. "
                            + "Depth e includes the zero difference.")),
                    Paragraph(Text(
                        "A decorated program ends at a leaf containing a decoded residue, "
                            + "or queries a center and continues according to its complete "
                            + "natural-number response. Eval(T,y) is the decoded leaf reached "
                            + "on y. Trace(T,y) is the complete center-response list after "
                            + "erasing the leaf labels. Every query contributes one entry.")),
                    Paragraph(Text(
                        "A(p,e,h,s,r) starts with h remaining digits and known prefix r "
                            + "at depth s. For h=0 it ends with decoded value r. Otherwise "
                            + "it tests centers r+a p^s in the order a=0,...,p-2. A response "
                            + "greater than s selects that digit; it calls A(p,e,h-1,s+1,"
                            + "r+a p^s). A response not greater than s advances a only. "
                            + "After all p-1 failures it selects digit p-1 without another "
                            + "query and makes the same recursive call. Both updated "
                            + "coordinates use the old s. Extra depth beyond s+1 is discarded.")),
                    Paragraph(Text(
                        "Legal(T,y) states along the actual query path that each stored "
                            + "prefix r equals y mod p^s and every response is at least its "
                            + "stored depth s. At a decoded leaf the stored center has saturated response e. With "
                            + "r=y mod p^s, the next digit is (floor(y/p^s) mod p). A query "
                            + "matches precisely that digit. All earlier failures preserve "
                            + "the lower bound on the untried digit. After p-1 failures "
                            + "only p-1 remains. Each selected digit gives the new prefix "
                            + "y mod p^(s+1). Induction proves the decoded value and the "
                            + "remaining budget h(p-1), including p=2 and y=0.")),
                    Paragraph(Text(
                        "The initial program is A(p,e,e,0,0), with no given digit. "
                            + "A matching final-digit response is saturated at e. A "
                            + "terminated program retains its decoded residue: padding "
                            + "further rounds with that residue as center yields known "
                            + "saturated responses without changing the decoded value."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Budget/ResidueLeafOptimality")),
        ]));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] args) => Call(s, args);
    private static Formula All(Formula x, Formula set, Formula body) =>
        Seq(Forall, Sp, x, Sp, InMacro, Sp, set, Comma, Sp, body);
    private static Formula Par(Formula x) => Seq(Left, Open, x, Right, Close);

    private static Formula Statement()
    {
        var p = V("p"); var e = V("e"); var h = V("h");
        var s = V("s"); var r = V("r"); var y = V("y");
        var nat = Seq(Mathbb, Grp(V("N")));
        var t = C("A", p, e, h, s, r);
        var prefix = Seq(C("mod", C("val", y), Seq(p, Caret, Grp(s))), Sp, Eq, Sp, r);
        var conclusion = Seq(C("Eval", t, y), Sp, Eq, Sp, y, Sp, Land, Sp,
            C("len", C("Trace", t, y)), Sp, Leq, Sp,
            h, Par(Seq(p, Minus, D(1))), Sp, Land, Sp, C("Legal", t, y));
        var body = All(h, nat, All(s, nat, All(r, nat,
            Seq(Par(Seq(s, Plus, h, Sp, Eq, Sp, e)), Sp, Rightarrow, Sp,
                All(y, C("ZMod", Seq(p, Caret, Grp(e))),
                    Seq(Par(prefix), Sp, Rightarrow, Sp, conclusion))))));
        return All(p, nat, All(e, nat,
            Seq(Par(Seq(C("Prime", p), Sp, Land, Sp, D(1), Sp, Leq, Sp, e)),
                Sp, Rightarrow, Sp, body)));
    }
}
