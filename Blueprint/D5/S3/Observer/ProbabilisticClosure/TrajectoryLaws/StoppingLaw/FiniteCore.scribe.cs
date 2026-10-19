using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw;

internal sealed class FiniteCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full finite stopping law determines constructors and geometry", H("A full finite stopping law determines constructors and geometry"), Blocks(
            Paragraph(Text("Observation retains the hidden endpoint value, optional output, return indicator and exact paid count. fullMass averages the two phase sections using a fair independent phase and the iid biased spins. lawWindow(T) contains the actual spin support of the tree and the target vertices. HasStoppingLaw equates every observation mass to stoppingMass, including the tuples of mass zero.")),
            Paragraph(Text("The input tree permits none leaves, repeated reads, separator reads, arbitrary binary branching and wrong output labels. A height cap and the full law first reconstruct its unpadded stopping comb. The recovered zero-prefix masses then determine its integer edge geometry.")),
            Describe.Lean(DescribeId.Create("finite-full-law-forces-stopping-path"), DeclarationHandle.Create(Prefix + "finite_full_law_forces_stopping_path"),
                H("Finite inverse stopping-law theorem"), StatementSource.FromAuthor(Disp(All("beta", N("Bias"), All("j", N("Bool"), All("k", N("Nat"), All("T", N("ReadTree"), Imp(Conj(Leq(D(1), N("k")), Leq(A("height", N("T")), N("k")), A("HasStoppingLaw", N("beta"), A("lawWindow", N("T")), N("j"), N("k"), N("T"))), Some("es", A("List", N("Int")), Conj(Equal(A("length", N("es")), N("k")), A("Nodup", N("es")), Some("L", N("Int"), Conj(Equal(N("T"), A("stopComb", A("mapAddresses", N("es"), A("not", N("j"))))), Equal(A("toFinset", N("es")), A("pathEdges", N("L"), N("k"))), A("notMem", A("toInt", N("j")), A("pathVertices", N("L"), N("k")))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("mapAddresses(es,phi) maps each edge e to the original integer address 2e+toInt(phi). Constructor reconstruction forces exactly k read nodes: a zero reply continues and a one reply returns a1, with final zero return a0. The edge list is duplicate-free, its set is a consecutive interval, and the target spin vertex lies outside that interval. Each prefix may extend either endpoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sourcelaw-observation"), DeclarationHandle.Create(Prefix + "sourceLaw_observation"),
                H("Infinite iid source agrees with the finite window"), StatementSource.FromAuthor(Disp(All("beta", N("Bias"), All("j", N("Bool"), All("T", N("ReadTree"), All("z", N("Observation"), Equal(A("real", A("sourceLaw", N("beta")), A("observationEvent", N("j"), N("T"), N("z"))), A("fullMass", N("beta"), A("lawWindow", N("T")), N("j"), N("T"), N("z"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("observationEvent(j,T,z) is the source event observation(j,phase,T,spins)=z. The source law is fairPhase.prod spinLaw. Finite coordinate projection identifies its probability with the finite-window fullMass, while the visible and hidden formulas keep the original endpoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-remote-read-section"), DeclarationHandle.Create(Prefix + "finite_remote_read_section"),
                H("A first remote read has the required prefix mass"), StatementSource.FromAuthor(Disp(All("beta", N("Bias"), All("j", N("Bool"), All("k", N("Nat"), All("T", N("ReadTree"), Imp(Conj(Leq(D(1), N("k")), Leq(A("height", N("T")), N("k")), A("HasStoppingLaw", N("beta"), A("lawWindow", N("T")), N("j"), N("k"), N("T"))), Some("m", N("Nat"), Conj(Leq(D(1), N("m")), Leq(N("m"), N("k")), Equal(A("remoteMass", N("beta"), A("lawWindow", N("T")), N("j"), PlusOf(TimesOf(D(2), N("k")), D(1)), N("T")), Divide(PlusOf(D(1), A("T", N("beta"), N("m"))), D(2))), Leq(Divide(PlusOf(D(1), A("T", N("beta"), N("k"))), D(2)), A("remoteMass", N("beta"), A("lawWindow", N("T")), N("j"), PlusOf(TimesOf(D(2), N("k")), D(1)), N("T")))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every permitted bias beta, endpoint j, k at least one and tree T of height at most k satisfying HasStoppingLaw in lawWindow(T), the remote-read source event has probability at least (1+T(k))/2. Remote means distance at least 2k+1 from j, and the proof concerns an actual executed read. The first remote node at position m is reached after m-1 zero replies; its phase-averaged mass is (1+T(m))/2, and antitonicity gives the stated lower bound."))), DescribeRole.Theorem),
            Paragraph(Text("Actual source events are measurable cylinder events supported on the finite tree window. Their finite and infinite product masses agree exactly.")))));
    private static Formula N(string name) => F.Seq(Operatorname, Grp(F.Id(name)));
    private static Formula A(string name, params Formula[] args)
    {
        var parts = new System.Collections.Generic.List<Formula> { N(name), Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.Add(F.Seq(Comma, Sp));
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return F.Seq(parts.ToArray());
    }
    private static Formula All(string name, Formula type, Formula body) =>
        F.Seq(Forall, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
    private static Formula Some(string name, Formula type, Formula body) =>
        F.Seq(Exists, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
    private static Formula Equal(Formula x, Formula y) => F.Seq(x, Sp, Eq, Sp, y);
    private static Formula Leq(Formula x, Formula y) => F.Seq(x, Sp, Le, Sp, y);
    private static Formula Imp(Formula x, Formula y) => F.Seq(Open, x, Close, Sp, To, Sp, Open, y, Close);
    private static Formula PlusOf(Formula x, Formula y) => F.Seq(Open, x, Sp, Plus, Sp, y, Close);
    private static Formula TimesOf(Formula x, Formula y) => F.Seq(Open, x, Sp, Star, Sp, y, Close);
    private static Formula Divide(Formula x, Formula y) => F.Seq(Frac, Grp(x), Grp(y));
    private static Formula Conj(params Formula[] xs)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) parts.Add(F.Seq(Sp, Land, Sp));
            parts.Add(F.Seq(Open, xs[i], Close));
        }
        return F.Seq(parts.ToArray());
    }
}
