using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativePayloadHistoryInstallationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativePayloadHistoryInstallation", H("Exact actual-history installation of native payloads"), Blocks(
            Describe.Lean(DescribeId.Create("native-payload-history-exact"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativePayloadHistoryInstallation.payload_history_exact"),
                H("Finite literal and positive records determine the whole payload"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Source is the native free ordered binary tree on alpha and beta. Native substitution sends alpha to beta and beta to the ordered pair (beta, alpha), and preserves pairs. A MixedExpr contains finite ground trees, a fixed natural substitution power of a named generator, and ordered pairs. The same generator name has one value throughout the expression.")),
                    Paragraph(Text("A literal record retains a natural epoch, an original address and one of the four ordinary replies. A positive record retains two epochs and two original addresses. Its independent native semantics requires both endpoints to be reached in the same actual source and their entire subtrees to agree. Holds conjoins the supplied finite list without removing repetitions. No record is interpreted by referring to the desired payload value.")),
                    Paragraph(Text("The compiler traverses the finite syntax at the supplied payload root p. An explicit pair emits its branch literal and recurses at the original left and right addresses. A ground emits the existing acquisitionTrace, including every constructor and terminal leaf. A decorated generator emits one positive link from the payload position at epoch zero to its supplied locator at that fixed epoch. Compilation receives neither the actual source nor the generator valuation.")),
                    Paragraph(Text("names lists the generator occurrences, including repeated names. The only premise identifies each occurring generator at its actual original locator in U. Unused names impose no premise. The generator type need not be finite or inhabited, locator addresses need not be distinct or prefix-free, and the payload root may be empty. NativeDepthPatterns.original_present_transport gives the recorded-epoch value of each originally reached generator.")),
                    Paragraph(Text("The conclusion is an exact equivalence between the generated history and the reached payload subtree with the interpreted value. The proof first establishes exact ground-trace reconstruction, using the unconditional native address-composition and root-readout clauses of ActualLeafHistoryRigidity.actual_address_geometry. Structural induction then combines ordered child reconstruction and the original generator transport. Terminal ground leaves forbid hidden extra descendants.")),
                    Paragraph(Text("Overlap between payload and generator addresses is allowed. It can make both sides of the equivalence false: a generator placed at the payload root cannot also equal the ordered pair of itself with alpha in a finite tree. Thus the theorem does not assert existence for arbitrary simultaneous placements. The locator premise is also essential: a value assigned independently of the actual generator subtree need not agree with the emitted link.")),
                    Paragraph(Text("For RankedExpr k m, use the generator type Fin k plus Fin m. Locate each rank generator at the right child of its atomic-role representative and each residual generator at its own representative. Assign the rank generator T(n) and the residual its finite tree. A decoration c then emits the original link to epoch c and evaluates to T(n+c). This application additionally requires the separate atomic-feedback correspondence to establish those original generator values.")),
                    Paragraph(Text("This is a native semantic compiler theorem obtained by ordinary finite structural induction; no literature-originality claim is made. It supplies the payload clause of the general acquired-fiber construction. Arbitrary-context exterior reconstruction, atomic feedback, cross-role inequalities, additional negative records, rank-only suffix refinements and explicit inverse laws remain distinct obligations. The theorem provides neither an observer-accessible equality port nor an arbitrary-policy decision procedure, resource bound or full acquired-fiber bijection."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource Statement()
    {
        var source = V("Source");
        var address = V("Address");
        var located = All("i", V("I"), Imp(
            Seq(V("i"), Sp, InMacro, Sp, Call("names", V("E"))),
            EqOf(Call("subtree", Call("loc", V("i")), V("U")),
                Call("some", Call("z", V("i"))))));
        var history = Call("Holds", V("U"), Call("compile", V("loc"), V("p"), V("E")));
        var payload = EqOf(Call("subtree", V("p"), V("U")),
            Call("some", Call("eval", V("z"), V("E"))));
        Formula result = Imp(located, Seq(Par(history), Sp, Iff, Sp, Par(payload)));
        result = All("z", Arr(V("I"), source), result);
        result = All("U", source, result);
        result = All("p", address, result);
        result = All("loc", Arr(V("I"), address), result);
        result = All("E", Call("MixedExpr", V("I")), result);
        result = All("I", V("Type"), result);
        return StatementSource.FromAuthor(Disp(result));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
