using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class DyadicForwardWaitingOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least worst-case forward waiting time for dyadic high-bit recovery "
            + "at the minimum binary query budget is attained by midpoint sensing.",
        H("Sharp Waiting for Dyadic High-Bit Recovery"),
        Blocks(
            Paragraph(Text(
                "Fix any natural j and known bit b in Fin(2), and put P=2^j. "
                    + "The original state is bP+r modulo 2P, with unknown 0<=r<P. "
                    + "After n forward unit evolutions, raw(P,b,n,r) is "
                    + "floor((bP+r+n)/P) modulo 2. The decoded bit read(P,b,n,r) "
                    + "is raw(P,b,n,r)+b+floor(n/P) modulo 2. Thus decoding retains "
                    + "both the initial bit and elapsed whole-period parity.")),
            Paragraph(Text(
                "Protocol(j) consists of early stopping leaves labelled by a recovered "
                    + "original residue, and query nodes containing a natural waiting increment "
                    + "and one continuation per observed bit. Each query reduces the remaining "
                    + "budget by one. A continuation depends only on previously acquired bits; "
                    + "no waiting choice has direct access to the unknown residue. Execution "
                    + "returns the leaf label and the final elapsed time. Adding bP to the recovered "
                    + "label recovers the original state.")),
            Paragraph(Text(
                "Correct(read,T,n,a,L) means that T, begun at time n, returns r for every "
                    + "a<=r<a+L. Bounds(P,j,read) is the set of natural W for which some "
                    + "T in Protocol(j) is correct on [0,P) from time zero and finishes by W "
                    + "on every such residue. Set W(0)=0 and W(j)=(j-1)2^j+1 for j>=1.")),
            Paragraph(Text(
                "M(P,d,a,n) stops with label a when d=0. Otherwise let m=a+2^(d-1), "
                    + "wait (P-m+P-(n mod P)) mod P, and read the sensor. The zero branch "
                    + "continues on [a,m), and the one branch on [m,a+2^d), with budget d-1 "
                    + "and the updated elapsed time. This is the earliest midpoint phase. "
                    + "Let T be the raw-bit controller obtained from M(P,j,0,0). It adds "
                    + "b+floor(n/P) modulo two to each newly observed "
                    + "bit before selecting the midpoint continuation. Write cut(P,n,r)=0 when "
                    + "r<P-(n mod P) and 1 otherwise, "
                    + "q(n,r)=raw(P,b,n,r), and Time(q,T,r) for the completion time from zero. "
                    + "Relabelling each branch by the known parity transports controllers in "
                    + "both directions and preserves both recovered labels and completion times.")),
            Describe.Lean(
                DescribeId.Create("dyadic-forward-waiting-optimality"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/DyadicForwardWaitingOptimality.dyadic_forward_waiting_optimality"),
                H("The attained least waiting bound and the physical readout formula"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Binary leaf capacity is saturated. If a query cut lies to either side "
                            + "of the candidate interval midpoint, one continuation must distinguish "
                            + "more than 2^(d-1) residues with only d-1 queries. Consequently every "
                            + "reachable nonterminal interval is bisected.")),
                    Paragraph(Text(
                        "For j>=1, along the single original residue P-1, the forced phases are "
                            + "2^(j-1),2^(j-2),...,1. Each strict decrease forces an additional "
                            + "whole period under forward evolution. The last query therefore "
                            + "occurs no earlier than (j-1)P+1. For midpoint sensing, each later "
                            + "increment is either 2^d or P-2^d when the next half-length is 2^d; "
                            + "induction proves exact recovery "
                            + "and the matching bound for every residue. When j=0, the stopped "
                            + "controller already identifies the sole residue without waiting. "
                            + "The argument applies separately to both known initial bits."))),
                DescribeRole.Theorem))));

    private static Formula ForAll(Formula name, Formula domain, Formula body) =>
        Seq(Forall, Sp, name, Sp, Colon, Sp, domain, Comma, Sp, body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Statement()
    {
        Formula j = F.Id("j"), b = F.Id("b"), p = F.Id("P"), n = F.Id("n"),
            r = F.Id("r"), read = F.Id("q"), t = F.Id("T");
        Formula sensorLaw = ForAll(n, Naturals(), ForAll(r, Naturals(), Seq(
            r, Sp, Lt, Sp, p, Sp, Implies, Sp, Grp(Seq(
                Call("raw", p, b, n, r), Sp, Eq, Sp,
                Call("mod", Grp(Seq(b, Sp, Plus, Sp, Call("div", n, p),
                    Sp, Plus, Sp, Call("cut", p, n, r))), D(2)), Sp, Land, Sp,
                Call("read", p, b, n, r), Sp, Eq, Sp, Call("cut", p, n, r))))));
        Formula cost = ForAll(r, Naturals(), Seq(r, Sp, Lt, Sp, p, Sp, Implies, Sp,
            Call("Time", read, t, r), Sp, Leq, Sp, Call("W", j)));
        Formula body = Seq(Open, sensorLaw, Close, Sp, Land, Sp,
            Call("IsLeast", Call("Bounds", p, j, read), Call("W", j)), Sp, Land, Sp,
            Call("Correct", read, t, D(0), D(0), p), Sp, Land, Sp, Open, cost, Close);
        return Disp(ForAll(j, Naturals(), ForAll(b, Call("Fin", D(2)), Grp(body))));
    }
}
