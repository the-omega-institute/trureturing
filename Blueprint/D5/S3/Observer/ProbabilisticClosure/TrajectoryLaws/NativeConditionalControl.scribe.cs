using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeConditionalControlDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), d = F.Id("d"), omega = F.Id("omega"), n = F.Id("n");
        Formula statement = All("c", F.Id("AcquiredNativeState"),
            All("d", F.Id("AcquiredNativeState"), All("omega", F.Id("Stream"),
            All("n", F.Id("Nat"), Seq(
                Call("control", c), Eq, Call("control", d), Rightarrow,
                Call("visible", Call("nativeDrive", c, omega, n)), Eq,
                Call("visible", Call("nativeDrive", d, omega, n)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Equal native controls give equal visible operation traces at every finite event count.",
            H("Native conditional continuation and control projection"), Blocks(
                Paragraph(Text("A full acquired native state contains the original control and registers, the payload-return bank and both acquired-letter counters. Stream is the raw natural-indexed sequence of Fin(2) letters. nativeDrive uses the original native transaction table. A Read advances the raw cursor by one; the matching Stop costs zero Reads. Visible retains the emitted operation list and successor control, including pending color and delivered status. It omits registers and numeric banks only from this projection.")),
                Describe.Lean(DescribeId.Create("drive-control"), DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl.drive_control"),
                    H("Control determines every finite visible trace"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The statement ranges over arbitrary pairs of full native states, every common raw stream and every natural event count, without a reachability assumption. Equal controls schedule the same operation and give equal successor controls. The recursive comparison applies this relation to the two actual successor states on the same shifted stream, then prepends their common operation. Failure, pending Stop and delivery are included. Equality of the projected trace does not assert equality of the hidden registers or return and count banks."))), DescribeRole.Theorem),
                Paragraph(Text("For depth k in PNat, rate(k)=fib(k+1)/fib(k+3) lies strictly between zero and one. jointLaw(mu) first draws one k from the arbitrary PMF mu and uses its raw Bernoulli law for the entire stream. nativeEvent(h,c) is the exact independently emitted initialized-history cylinder. likelihood(h,k) is the product mass of every acquired Read, including rejected seed pairs, returns and partial cuts; its positive mixture normalizer defines posterior(mu,h,c). No support bound, finite mean or future acceptance event is assumed.")),
                Paragraph(Text("The conditional joint law of the unchanged depth and the unread raw tail equals jointLaw(posterior). The prefix cylinder and tail sigma-algebras involve disjoint raw coordinates, so their fixed-depth product factorization survives the countable posterior mixture. Native stopping comparisons keep the full state, marker writes and the unique unpaid Stop. This conditional-law identity and the control projection serve different purposes: the former preserves the source law and the latter justifies omitting past held fields from the permitted residual transcript.")))));
    }

    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
