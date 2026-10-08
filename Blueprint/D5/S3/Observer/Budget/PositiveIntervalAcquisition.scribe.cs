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

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Statement()
    {
        Formula p = F.Id("p"), P = F.Id("P"), T = F.Id("T"), b = F.Id("b"),
            n = F.Id("n"), r = F.Id("r"), w = F.Id("w");
        Formula h = Call("clog", D(2), P);
        Formula read = Call("Decoded", p, P, b);
        Formula path = Call("Waits", read, T, D(0), r);
        Formula law = All(b, N(), All(n, N(), All(r, N(), Seq(
            r, Sp, Lt, Sp, P, Sp, Implies, Sp, Grp(Seq(
                Call("div", Call("mod", Seq(b, Times, P, Plus, r, Plus, n), Seq(p, Times, P)), P),
                Sp, Eq, Sp, Call("mod", Seq(b, Plus, Call("div", n, P), Plus,
                    Call("Cut", P, n, r)), p), Sp, Land, Sp,
                Call("Decoded", p, P, b, n, r), Sp, Eq, Sp, Call("Cut", P, n, r)))))));
        Formula waits = All(w, N(), Seq(w, Sp, In, Sp, path, Sp, Implies, Sp,
            Grp(Seq(D(0), Sp, Lt, Sp, w, Sp, Land, Sp, w, Sp, Lt, Sp, P))));
        Formula behavior = All(b, N(), All(r, N(), Seq(r, Sp, Lt, Sp, P, Sp, Implies, Sp,
            Grp(Seq(Call("Answer", read, T, D(0), r), Sp, Eq, Sp, r, Sp, Land, Sp,
                Call("Time", read, T, D(0), r), Sp, Leq, Sp,
                h, Times, Grp(Seq(P, Minus, D(1))), Sp, Land, Sp,
                Call("length", path), Sp, Leq, Sp, h, Sp, Land, Sp, waits)))));
        Formula attained = All(b, N(), Seq(
            Call("length", Call("Waits", read, T, D(0), Seq(P, Minus, D(1)))),
            Sp, Eq, Sp, h));
        Formula singleton = Seq(P, Sp, Eq, Sp, D(1), Sp, Implies, Sp,
            T, Sp, Eq, Sp, Call("Stop", D(0)));
        return Disp(All(p, N(), All(P, N(), Seq(
            Grp(Seq(D(2), Sp, Leq, Sp, p, Sp, Land, Sp, D(0), Sp, Lt, Sp, P)),
            Sp, Implies, Sp, Exists, Sp, T, Sp, Colon, Sp, Call("Protocol", h), Comma, Sp,
            Grp(Seq(law, Sp, Land, Sp, behavior, Sp, Land, Sp, attained, Sp, Land, Sp,
                Grp(singleton)))))));
    }
}
