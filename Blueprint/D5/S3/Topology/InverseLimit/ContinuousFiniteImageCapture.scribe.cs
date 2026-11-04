using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;
internal sealed class ContinuousFiniteImageCaptureDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Statement() => Disp(All("inputs", V("OriginalLaunchInputs"),
        Imp(Call("OntoTablesAndLiteralLaunchReadback", V("inputs")),
            All("f", Call("ClosedDomainContinuousMap", Call("LiteralLimit", V("inputs"))),
                Imp(And(Call("InfiniteRange", V("f")), Call("DisjointDomainRange", V("f"))),
                    Ex("capture", V("OriginalWholeDiracCapture"),
                        And(Call("OriginalLaunchAndIntrinsicDelayedPredicate", V("inputs"), V("f"), V("capture")),
                            Call("EveryTargetDiracWitnessIsProjectedImage", V("inputs"), V("f"), V("capture")))))))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original exhaustive birth tables and actual ordinary launch readback capture both whole Dirac sequences under continuity alone.",
        H("Intrinsic continuous-map Dirac capture"), Blocks(
            Describe.Lean(DescribeId.Create("exists-original-dirac-capture"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/ContinuousFiniteImageCapture.exists_original_dirac_capture"),
                H("One original launch and two whole-sequence labels"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(Paragraph(Text(
                    "OriginalLaunchInputs means exactly H : SignedProperLimit.Prefix(omega-one); original onto tables U for support families, nu for BornData on V, and P for clopens on every stage at or above omega; the fixed Nat pair decoder; the prescribed lower bound; and literal original ordinary launch readback. "
                    + "That readback says that when the fixed CofinalTaskSchedule reservation at theta is (b,i), with b,i < theta and omega <= b, V(theta) is the pullback of U(b,i) along the actual restriction. No capture, delayed event or final conclusion is assumed. The limit is H.LimitSpace, the literal subspace of the original Boolean coordinate cube.")),
                    Paragraph(Text(
                    "For any closed domain A, continuous f : A -> H.LimitSpace, infinite range and disjoint domain and range, the theorem produces b above the requested base, an ordinary reservation theta > b,i, a single source point list x, original labels s and t for the two entire Dirac sequences, and one code k in the original P enumeration. "
                    + "The coded clopens are disjoint. Every target projection belongs to both V(theta,n) and the second clopen, the original source measures vanish in variation outside the first clopen, and both nu equalities hold for every n. Any alternative target point list whose signed Diracs equal nu(theta,t,n) is exactly the projected f-image list.")),
                    Paragraph(Text(
                    "SynchronizedClopenSupports supplies disjoint ambient clopens containing both markers under continuity alone. CountableClopenReflection reflects that whole family and the separator with its complement at one proper b. CofinalTaskSchedule supplies a later actual ordinary reservation; literal launch readback retains the same supports. "
                    + "SignedBirthEnumeration.pointBornData reuses the original regular Dirac construction for the supplied whole point lists; surjectivity chooses one label for each whole sequence. Original clopen surjectivity and the fixed decoder supply k. Mathlib's signed-measure conversion equality and Dirac injectivity force equality of every target witness. There is no termwise relabelling and no metric on the final uncountable cube.")),
                    Paragraph(Text(
                    "Application: these are precisely the intrinsic original-birth data needed by the signed delayed branch. Once the actual raw history and its birth/arrival readback are supplied, the same executed event must supply its clopen and replacement J. The proper-stage continuous-preimage obstruction then excludes the event for a continuous infinite-image map to a disjoint complement. This theorem alone does not construct that history or establish the final finite-image, anti-homeomorphism or CH Talagrand endpoint."))), DescribeRole.Theorem))));
}
