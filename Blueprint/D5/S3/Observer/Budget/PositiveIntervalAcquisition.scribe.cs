using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class PositiveIntervalAcquisitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty finite low-digit interval can be recovered by forward sensing "
            + "with logarithmically many subsequent reads and strictly positive waits.",
        H("Positive Forward Sensing on Arbitrary Intervals"),
        Blocks(
            Paragraph(Text(
                "Let p>=2 and P>0 be natural numbers, H=clog(2,P), and B=H(P-1). "
                    + "Protocol(H) is the binary query tree with early stopping leaves and "
                    + "a waiting increment at each query. Its execution returns the recovered "
                    + "low residue and final elapsed count. A retained first digit b together "
                    + "with a low residue r describes the initial source bP+r modulo pP.")),
            Paragraph(Text(
                "The physical digit at elapsed count n is floor(((bP+r+n) mod pP)/P). "
                    + "Decoded(p,P,b,n,r) is zero when this digit equals (b+floor(n/P)) mod p, "
                    + "and one otherwise. Cut(P,n,r) is zero for r<P-(n mod P), and one otherwise. "
                    + "Thus Decoded uses only the physical answer, retained digit, and elapsed count.")),
            Paragraph(Text(
                "Acquire(P,d,l,u,n) stops at l for a singleton half-open interval [l,u). "
                    + "Otherwise it splits at m=floor((l+u)/2), waits the strictly positive "
                    + "forward distance to phase P-m, and continues on [l,m) or [m,u). "
                    + "The list Waits records precisely the successive waiting increments "
                    + "on an execution. T=Acquire(P,H,0,P,0) is independent of b. "
                    + "Recovery of r also recovers bP+r and the final current residue "
                    + "(bP+r+n_final) mod pP. This tree description counts subsequent reads; "
                    + "the initial read acquiring b contributes one further read.")),
            Describe.Lean(
                DescribeId.Create("interval-positive-phase"),
                DeclarationHandle.Create("D5/S3/Observer/Budget/PositiveIntervalAcquisition.interval_wait"),
                H("Endpoint alignment gives a strictly positive midpoint wait"),
                StatementSource.FromAuthor(IntervalStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For l<u<=P and l+1<u, put m=floor((l+u)/2). If n modulo P "
                        + "equals (P-l) modulo P or (P-u) modulo P, then m is strictly "
                        + "between the endpoints. The positive forward distance w to P-m "
                        + "satisfies 0<w<P and (n+w) modulo P equals P-m."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("positive-interval-acquisition"),
                DeclarationHandle.Create("D5/S3/Observer/Budget/PositiveIntervalAcquisition.result"),
                H("Shared interval tree, physical digit law, costs, and attained depth"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each live interval the elapsed phase is aligned with one endpoint. "
                        + "The midpoint lies strictly between both endpoints, so the next phase "
                        + "differs and its positive waiting distance is below P. The physical "
                        + "digit distinguishes exactly the two subintervals, including when p=2. "
                        + "Both subintervals fit the remaining binary depth. The rightmost residue "
                        + "always follows the larger half, whose upper logarithm drops by one, "
                        + "so its read count attains H. A singleton needs no subsequent query."))),
                DescribeRole.Theorem))));

    private static Formula All(Formula x, Formula domain, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, domain, Comma, Sp, body);

    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula IntervalStatement()
    {
        Formula P = F.Id("P"), l = F.Id("l"), u = F.Id("u"), n = F.Id("n"),
            m = Call("div", Seq(l, Sp, Plus, Sp, u), D(2));
        Formula w = Call("waitTo", P, n, Seq(P, Sp, Minus, Sp, m));
        Formula phase = Call("mod", n, P);
        Formula assumptions = Seq(l, Sp, Lt, Sp, u, Sp, Land, Sp, u, Sp, Leq, Sp, P, Sp, Land, Sp,
            l, Sp, Plus, Sp, D(1), Sp, Lt, Sp, u, Sp, Land, Sp,
            Par(Seq(phase, Sp, Eq, Sp, Call("mod", Seq(P, Sp, Minus, Sp, l), P), Sp, Lor, Sp,
                phase, Sp, Eq, Sp, Call("mod", Seq(P, Sp, Minus, Sp, u), P))));
        Formula conclusion = Seq(l, Sp, Lt, Sp, m, Sp, Land, Sp, m, Sp, Lt, Sp, u, Sp, Land, Sp, D(0), Sp, Lt, Sp, w,
            Sp, Land, Sp, w, Sp, Lt, Sp, P, Sp, Land, Sp, Call("mod", Seq(n, Sp, Plus, Sp, w), P), Sp, Eq, Sp, P, Sp, Minus, Sp, m);
        return Disp(All(P, N(), All(l, N(), All(u, N(), All(n, N(),
            Seq(Par(assumptions), Sp, Implies, Sp, Par(conclusion)))))));
    }

    private static Formula Statement()
    {
        Formula p = F.Id("p"), P = F.Id("P"), T = F.Id("T"), b = F.Id("b"),
            n = F.Id("n"), r = F.Id("r"), w = F.Id("w");
        Formula h = Call("clog", D(2), P);
        Formula read = Call("Decoded", p, P, b);
        Formula path = Call("Waits", read, T, D(0), r);
        Formula law = All(b, N(), All(n, N(), All(r, N(), Seq(
            r, Sp, Lt, Sp, P, Sp, Implies, Sp, Par(Seq(
                Call("div", Call("mod", Seq(b, Sp, Times, Sp, P, Sp, Plus, Sp, r, Sp, Plus, Sp, n), Seq(p, Sp, Times, Sp, P)), P),
                Sp, Eq, Sp, Call("mod", Seq(b, Sp, Plus, Sp, Call("div", n, P), Sp, Plus, Sp,
                    Call("Cut", P, n, r)), p), Sp, Land, Sp,
                Call("Decoded", p, P, b, n, r), Sp, Eq, Sp, Call("Cut", P, n, r)))))));
        Formula waits = All(w, N(), Seq(w, Sp, InMacro, Sp, path, Sp, Implies, Sp,
            Par(Seq(D(0), Sp, Lt, Sp, w, Sp, Land, Sp, w, Sp, Lt, Sp, P))));
        Formula behavior = All(b, N(), All(r, N(), Seq(r, Sp, Lt, Sp, P, Sp, Implies, Sp,
            Par(Seq(Call("Answer", read, T, D(0), r), Sp, Eq, Sp, r, Sp, Land, Sp,
                Call("Time", read, T, D(0), r), Sp, Leq, Sp,
                h, Sp, Times, Sp, Par(Seq(P, Sp, Minus, Sp, D(1))), Sp, Land, Sp,
                Call("length", path), Sp, Leq, Sp, h, Sp, Land, Sp, waits)))));
        Formula attained = All(b, N(), Seq(
            Call("length", Call("Waits", read, T, D(0), Seq(P, Sp, Minus, Sp, D(1)))),
            Sp, Eq, Sp, h));
        Formula singleton = Seq(P, Sp, Eq, Sp, D(1), Sp, Implies, Sp,
            T, Sp, Eq, Sp, Call("Stop", D(0)));
        return Disp(All(p, N(), All(P, N(), Seq(
            Par(Seq(D(2), Sp, Leq, Sp, p, Sp, Land, Sp, D(0), Sp, Lt, Sp, P)),
            Sp, Implies, Sp, Exists, Sp, T, Sp, Colon, Sp, Call("Protocol", h), Comma, Sp,
            Par(Seq(T, Sp, Eq, Sp, Call("Acquire", P, h, D(0), P, D(0)),
                Sp, Land, Sp, Par(law), Sp, Land, Sp, Par(behavior), Sp, Land, Sp, Par(attained), Sp, Land, Sp,
                Par(singleton)))))));
    }
}
