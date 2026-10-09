using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeAcquiredPrefixCylinderDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.";

    public DocumentDefinition Create()
    {
        Formula h = F.Id("h"), c = F.Id("c"), omega = F.Id("omega");
        Formula k = F.Id("k"), n = F.Id("n"), nf = F.Id("nf");
        Formula history = Call("List", F.Id("Operation"));
        Formula state = F.Id("AcquiredNativeState"), stream = F.Id("Stream");
        Formula nat = F.Id("Nat");
        Formula paid = Call("length", Call("readLetters", h));
        Formula eventEquation = Equal(
            Call("nativeDrive", F.Id("initial"), omega, Call("length", h)),
            Call("some", Tuple(h, c, k)));
        Formula cylinder = All("h", history, All("c", state,
            All("omega", stream, All("k", nat,
                Seq(Open, eventEquation, Close, Leftrightarrow, Open,
                    Equal(Call("run", h), Call("some", c)), Land, Sp,
                    Call("Prefix", omega, Call("readLetters", h)), Land, Sp,
                    Equal(k, paid), Close)))));
        Formula restart = Equal(
            Call("nativeDrive", F.Id("initial"), omega,
                Seq(Call("length", h), Plus, n)),
            Call("map", Call("pack", h, k),
                Call("nativeDrive", c, Call("rawTail", omega, k), n)));
        Formula fields = Seq(Exists, Sp, nf, Colon, F.Id("PrefixForm"), Comma, Sp,
            Open, Equal(Call("render", nf), h), Land, Sp,
            Equal(c, Call("reconstruct", nf)), Land, Sp, Call("PrefixFacts", nf, c), Close);
        Formula resumption = All("h", history, All("c", state,
            All("omega", stream, All("k", nat, All("n", nat,
                Imp(eventEquation, Seq(Equal(k, paid), Land, Sp, restart, Land, Sp, fields)))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Native stream execution has exact finite history cylinders and resumes at its unread tail.",
            H("Native acquired-prefix cylinders and resumption"), Blocks(
                Paragraph(Text("Stream is the raw function from natural indices to Letter, with Letter=Fin(2). readLetters erases only Stop operations from an operation list: it retains every acquired letter in its original order, including equal-pair seed rejections, accepted pairs, payload returns and partial cuts. rawTail(omega,k)(i)=omega(i+k). A Read has readCost one and a Stop has readCost zero.")),
                Paragraph(Text("nextOperation reads the first raw letter at seed, early-payload and active-fourth controls. At pending b it selects only Stop b; delivered selects no event. nextNative performs that scheduled operation with the original nativeStep. nativeDrive(c,omega,n) executes exactly n scheduled events: zero returns some([],c,0); a successor executes nextNative, recursively drives its full successor state on rawTail(omega,readCost(op)), then prepends op and adds its Read cost. Any unavailable event or failed transaction returns none. The operation history is an output of this recursion. The event bound n and the returned paid cursor k are distinct mathematical indices.")),
                Node("native-acquired-prefix-cylinder", "native_acquired_prefix_cylinder",
                    "Exact independently emitted history fibers", cylinder,
                    "The equality is universal in the finite operation history, full native state, raw stream and paid cursor. A history has a nonempty fiber exactly when its original run is legal, and its raw source fiber is precisely Prefix(omega,readLetters(h)). Every illegal history has an empty fiber. No completion assumption or uniform history bound occurs. Induction on the number of emitted events compares each independently scheduled nativeStep with supplied-list execute. For Read, the prefix condition splits into its first letter and the prefix of the raw tail; for Stop, neither letters nor paid cursor change. The returned full state is exactly the state of the original transaction fold, including every register and both numeric banks."),
                Paragraph(Text("In the next formula, map is Option.map and pack(h,k)(v,d,j)=(h++v,d,k+j). The history concatenation joins the original prefix and newly emitted suffix; the full successor state d is unchanged by pack. PrefixFacts and reconstruct are the existing native reconstruction predicate and calculation, including ordered rejected pairs as form data, actual seed, payload phase, unbounded returns, paid letter counts, original writes, the post-third latch and held records. Those form data are mathematical descriptions, not additional retained native fields.")),
                Node("native-acquired-prefix-resumption", "native_acquired_prefix_resumption",
                    "Restart with the full state and untouched raw tail", resumption,
                    "On any emitted prefix event, the returned paid cursor equals length(readLetters(h)). For every further event count n, driving from the original initialization for length(h)+n events equals driving from its full returned state on exactly rawTail(omega,k), then joining the histories and paid cursors. The equality includes failure of an overlong execution. Induction on the prefix event count proves the driver concatenation identity, using rawTail(rawTail(omega,a),b)=rawTail(omega,a+b). The cylinder identity supplies the exact paid cursor and legal run. The unique existing native normal form then supplies c=reconstruct(nf) and every PrefixFacts field. At pending the next event is its matching zero-cost Stop; after delivery every positive event count fails and zero events retain the state."),
                Paragraph(Text("All finite cuts are included, with both seeds, arbitrary rejected-pair order, arbitrary early and fourth-segment returns, pending and delivered states, and illegal operations excluded by the original transaction permissions. This deterministic statement does not supply a probability law for a shared hidden depth, a posterior for a finite or countable prior, a conditional-law identification, or a complete measurable continuation and recovery theorem.")))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(x), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Open, premise, Close, Rightarrow, Open, body, Close);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Tuple(Formula x, Formula y, Formula z) =>
        Seq(Open, x, Comma, y, Comma, z, Close);
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
