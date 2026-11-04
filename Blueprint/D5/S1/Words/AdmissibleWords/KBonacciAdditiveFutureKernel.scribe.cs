using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciAdditiveFutureKernelDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Op(name), [.. args]);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, V(name), Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(left, Sp, relation, Sp, right);
    private static Formula And(params Formula[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i != 0) items.Add(Seq(Sp, Land, Sp));
            items.Add(Seq(Open, parts[i], Close));
        }
        return Seq([.. items]);
    }

    private static Formula Statement()
    {
        var k = V("k");
        var w = V("w");
        var v = V("v");
        var h = V("h");
        var x = V("x");
        var lam = V("lambda");
        var sw = Call("scan", k, w);
        var sv = Call("scan", k, v);
        var bothReject = And(Rel(sw, Eq, Op("none")), Rel(sv, Eq, Op("none")));
        var bothLive = Seq(Exists, Sp, V("s"), Comma, Sp, Exists, Sp, V("t"), Comma, Sp,
            And(Rel(sw, Eq, Call("some", V("s"))), Rel(sv, Eq, Call("some", V("t"))),
                Call("SignatureEq", x, lam, k, h, w, V("s"), v, V("t"))));
        var rhs = Seq(Open, bothReject, Close, Sp, Lor, Sp, Open, bothLive, Close);
        var statement = Rel(Call("NativeKernel", x, lam, k, h, w, v), Iff, rhs);
        var word = Call("List", Op("Bool"));
        var body = All("x", V("C"), All("lambda", Call("AddMonoidHom", V("C"), V("B")),
            All("k", Nat, Seq(Rel(D(2), Leq, k), Sp, Implies, Sp,
                All("h", Nat, All("w", word, All("v", word, statement)))))));
        return All("C", Op("Type"), All("B", Op("Type"),
            Seq(OpenBracket, Call("CommRing", V("C")), CloseBracket, Sp,
                OpenBracket, Call("AddCommGroup", V("B")), CloseBracket, Comma, Sp, body)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite future equality for actual binary histories is characterized by the current "
            + "additive output, the truncated rejection distance and the available coefficient window.",
        H("Additive responses of actual binary histories"),
        Blocks(
            Paragraph(Text(
                "Let C be a commutative ring, x an element of C, and lambda an additive "
                    + "homomorphism from C to an arbitrary abelian group B. No ring structure "
                    + "on B and no surjectivity or nonzero condition on lambda is required. "
                    + "For the canonical modular probes one takes C to be the image of the "
                    + "single polynomial map into the probe quotients, with x the image of X. "
                    + "This application retains composite moduli and makes no product assertion "
                    + "about the common image.")),
            Paragraph(Text(
                "A history is a finite list of Boolean bits read from low to high degree. "
                    + "Its polynomial value is the sum of x^j over its true positions. The "
                    + "current output is lambda of this value when DBonacciAdmissible accepts "
                    + "the history for the original forbidden run of k true bits, and none "
                    + "otherwise. The scanner has states s in Fin k, resets s to zero on false, "
                    + "increments s on a legal true bit, and rejects at s=k-1. Its partial run "
                    + "composes by Option.bind, so rejection persists under every extension.")),
            Paragraph(Text(
                "Put c_n=lambda(x^n). For two accepted histories w and v, with scanner states "
                    + "s and t and lengths n and m, SignatureEq means all three conditions: "
                    + "their current additive values agree; min(k-s,h+1)=min(k-t,h+1); and "
                    + "c_(n+j)=c_(m+j) for every j<h satisfying s+1<k or j>0. At h=0 "
                    + "the latter conditions are automatic. For positive h the truncated "
                    + "distances already distinguish a terminal tail from a nonterminal tail. "
                    + "A nonterminal tail therefore exposes the entire h-coordinate window; "
                    + "a terminal tail exposes only coordinates one through h-1.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-additive-actual-history-kernel-signature"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciAdditiveFutureKernel."
                        + "actual_history_kernel_signature"),
                H("The complete finite future signature"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "NativeKernel tests every binary suffix of length at most h, including "
                            + "the empty word and suffixes that lead to rejection. Both rejected "
                            + "histories have equal responses. A rejected history and an "
                            + "accepted history differ already at the empty suffix.")),
                    Paragraph(Text(
                        "For accepted histories, the proof proceeds by the remaining suffix "
                            + "budget. A false first bit resets both tails and advances both "
                            + "coefficient positions. A true first bit rejects a terminal tail, "
                            + "while a nonterminal tail adds its current coefficient and "
                            + "increments the tail. The empty suffix fixes the current value; "
                            + "additive cancellation recovers the first coefficient whenever "
                            + "a true step is legal. The false branch supplies every later "
                            + "window coordinate. These two branches give necessity and "
                            + "sufficiency of the truncated rejection distance and the stated "
                            + "window, including k=2, h=0 and terminal tails.")),
                    Paragraph(Text(
                        "The native response is derived from the original scanner on actual "
                            + "concatenated words. Additivity turns the actual polynomial sum "
                            + "into the coefficient sum, and splitting that sum at the history "
                            + "length yields the current value plus the shifted suffix value. "
                            + "No joint realization of independently selected records is "
                            + "assumed by this statement."))),
                DescribeRole.Theorem))));
}
