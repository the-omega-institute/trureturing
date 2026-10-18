using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition;

internal sealed class NativeSelectedRARecordSoundnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete selected rows at their actual successful guard validation.",
        H("Authentic validation and the retained row"), Blocks(
            Paragraph(Text("The source register changes only by the fixed substitution. "
                + "A guard address reaches an actual alpha or beta leaf. Existing subtree addresses survive substitution, "
                + "and intrinsic depth increases by one at every update. The same leaf reply at the same address therefore cannot recur after a positive number of updates.")),
            Def("recordBytes", "The complete byte row",
                "The root cut has the constant four-cell row. The child cut has a literal leaf row on a leaf source, "
                + "or the two fully addressed holes followed by the equality bit and row terminator on a branch source. "
                + "The equality bit retains both diagonal pairs and both off-diagonal memberships or nonmemberships."),
            Def("decodeRow", "Literal exterior and complete partition",
                "The decoder checks the whole fixed-alphabet row and its selected cut. Valid rows decode to the literal exterior and full finite hole partition; all other rows are rejected. No absent operand is converted into a negative comparison."),
            Def("Candidate", "The authentic guard source",
                "There are an actual guard source V and a natural update count k with current source equal to the kth substitution iterate of V. "
                + "The saved guard is an actual leaf reply in V. When k is zero, a finite update-free actual prefix leads from the fresh guard exit to the current candidate configuration. "
                + "Positive k asserts no accuracy for the partly acquired candidate row. These objects occur only in the proof."),
            Def("Captured", "The actual successful validation event",
                "There exist an earlier event v and its actual Work w. The schedule executes an observer step at v while the call is pending; its whole configuration is active with the same selected cut, control twenty five and the retained row. "
                + "Reading the actual source at w's guard address returns w's saved guard reply. The row is exactly recordBytes for that same actual source and decodes to its complete literal record. "
                + "At every later observer index before the stated boundary, the actual instruction is local or Return. Thus no later Read intervenes."),
            Def("Certified", "Body and cleanup conditions",
                "Body phases retain an authentic candidate. Cleanup and ready configurations retain the certificate of their actual successful validation. Guard search and reset use the reachable workspace conditions of the native scanner."),
            Describe.Lean(DescribeId.Create("native-selected-ra-returning-capture"),
                DeclarationHandle.Create(Prefix + "returning_capture"),
                H("Every ready row has an authentic complete capture"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every source, active event schedule and finite prefix, reaching the whole ready configuration implies Captured. "
                    + "A successful validation forces the authentic guard epoch to be zero. The intervening actual body therefore has a stationary execution on the validation source. "
                    + "Determinism compares it with the actual stationary root, leaf or paired-subtree execution, including the full row and its partition sign. "
                    + "Cleanup preserves the row and performs only local instructions before the separate Return. Independent writer updates after validation do not alter the retained row's designated capture source."))),
                DescribeRole.Theorem),
            Def("eventSchedule", "Writer flags of the complete raw word",
                "At an index within the word, the schedule is true exactly for an independent update. Every observer event has false flag, and indices after the finite word also have false flag. The actual legal word retains every local step, Read and separate Return."),
            Describe.Lean(DescribeId.Create("native-selected-ra-all-returning-histories"),
                DeclarationHandle.Create(Prefix + "all_returning_histories"),
                H("Every legal returning raw history has its complete actual record"), StatementSource.FromAuthor(RawStatement()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every legal finite Run from entry to the whole ready row, Captured holds at the raw word's length under its own eventSchedule. "
                    + "Induction on the actual Run maps each independent write, local instruction, authentic Read and Return to exactly one trajectory event. "
                    + "The shifted-trajectory identity retains the actual intermediate world. The resulting certificate identifies the last successful validation Read in that same execution, and the complete literal record at its actual source."))),
                DescribeRole.Theorem))));
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-selected-ra-sound-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string n) => F.Id(n);
    private static Formula Op(string n) => Seq(Operatorname, Grp(V(n)));
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Op(n), [.. a]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula RawStatement()
    {
        Formula run = Call("Run", Op("step"), Op("entry"), V("u"), V("h"), Call("ready", V("q"), V("r")));
        Formula result = Call("Captured", V("u"), Call("eventSchedule", V("h")), Call("length", V("h")), V("q"), V("r"));
        return Disp(All("u", Op("Source"), All("h", Op("Word"), All("q", Op("Bool"),
            All("r", Call("List", Op("Cell")), Seq(Par(run), Sp, Implies, Sp, result))))));
    }
    private static Formula Statement()
    {
        Formula world = Call("trajectory", V("s"), Call("world", Op("entry"), V("u"), Op("false")), V("n"));
        Formula ready = Seq(Call("config", world), Sp, Eq, Sp, Call("ready", V("q"), V("r")));
        Formula result = Seq(Par(ready), Sp, Implies, Sp, Call("Captured", V("u"), V("s"), V("n"), V("q"), V("r")));
        return Disp(All("u", Op("Source"), All("s", Seq(Op("Nat"), Sp, To, Sp, Op("Bool")),
            All("n", Op("Nat"), All("q", Op("Bool"), All("r", Call("List", Op("Cell")), result))))));
    }
}
