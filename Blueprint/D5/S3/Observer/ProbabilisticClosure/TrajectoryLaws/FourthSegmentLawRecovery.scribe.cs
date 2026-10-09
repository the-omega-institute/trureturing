using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FourthSegmentLawRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.";

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), s = F.Id("s"), omega = F.Id("omega"), w = F.Id("w");
        Formula state = F.Id("AcquiredNativeState"), phase = F.Id("ActivePhase");
        Formula active = Equal(Call("control", c), Call("fourthActive", s));
        Formula renderer = Equal(Call("transcript", c, omega),
            Call("reconstructTranscript", s, Call("stoppedReadWord", s, omega)));
        Formula mu = F.Id("mu"), h = F.Id("h");
        Formula legal = Equal(Call("run", h), Call("some", c));
        Formula transport = Equal(Call("transcriptLaw", mu, h, c),
            Call("map", Call("reconstructTranscript", s),
                Call("wordMixture", Call("posterior", mu, h, c), s)));
        Formula d = F.Id("d"), t = F.Id("t"), rho = F.Id("rho"), g = F.Id("g");
        Formula laws = Equal(Call("lengthLaw", mu, h, c, s), Call("lengthLaw", rho, g, d, t));
        Formula transcripts = Equal(Call("transcriptLaw", mu, h, c), Call("transcriptLaw", rho, g, d));
        Formula statistics = Seq(Equal(s, t), Land, Sp,
            Equal(Call("posterior", mu, h, c), Call("posterior", rho, g, d)));
        Formula domain = Seq(legal, Land, Sp, Equal(Call("run", g), Call("some", d)),
            Land, Sp, active, Land, Sp, Equal(Call("control", d), Call("fourthActive", t)));
        Formula equivalences = Seq(Open, laws, Leftrightarrow, Sp, statistics, Close, Land, Sp,
            Open, laws, Leftrightarrow, Sp, transcripts, Close, Land, Sp,
            Open, transcripts, Leftrightarrow, Sp, statistics, Close);
        Formula recovery = All("mu", Call("PMF", F.Id("PNat")),
            All("rho", Call("PMF", F.Id("PNat")), All("h", Call("List", F.Id("Operation")),
            All("g", Call("List", F.Id("Operation")), All("c", state, All("d", state,
            All("s", phase, All("t", phase, Imp(domain, equivalences)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Original active-fourth length laws determine phase, the countable conditional depth distribution and the permitted residual transcript law.",
            H("Fourth-segment residual laws and depth recovery"), Blocks(
                Paragraph(Text("The domain is every legal initialized finite history whose full native control is fourth active p or beta, with any installed PMF on PNat. The same latent depth governs all acquired and future Reads. Conditioning uses the actual native history cylinder. transcript(c,omega)(n) records the projected native execution at every finite event budget, including actual Read letters, active and pending controls, the matching original Stop and delivery. Past held registers are absent from this projection; their erasure is justified by the all-budget control relation, while the underlying native execution retains them.")),
                Node("stopped-transcript", "stopped_transcript", "The complete stopped transcript",
                    All("c", state, All("s", phase, All("omega", F.Id("Stream"),
                    All("w", Call("List", F.Id("Letter")), Imp(Seq(active, Land, Sp,
                        Equal(Call("stoppedReadWord", s, omega), Call("some", w))),
                        Equal(Call("transcript", c, omega), Call("reconstructTranscript", s, Call("some", w)))))))),
                    "A completed word fixes all earlier raw letters and the full native state after its original Stop. Earlier budgets agree by prefix dependence, the Stop budget agrees by the full-state stopping correspondence, and every longer budget fails after delivery. Equal controls then replace the actual full state by the canonical phase state in the projected transcript."),
                Node("residual-renderer", "residual_renderer_all_paths", "The residual renderer on every stream",
                    All("c", state, All("s", phase, All("omega", F.Id("Stream"), Imp(active, renderer)))),
                    "The finite-word case uses the stopped transcript identity. In the none case, the raw stream is the unique infinite return tail and the control relation applies at every finite budget. This pointwise identity includes noncompletion rather than conditioning it away."),
                Node("residual-law", "residual_law_transport", "Transport of the actual conditional residual law",
                    All("mu", Call("PMF", F.Id("PNat")), All("h", Call("List", F.Id("Operation")),
                    All("c", state, All("s", phase, Imp(Seq(legal, Land, Sp, active), transport))))),
                    "The countable stopped-word carrier makes its renderer measurable. The unchanged-depth conditional-tail identity gives the posterior word mixture. Composing its actual pushforward with the all-path renderer gives the residual transcript law. The original zero-mass noncompletion theorem applies at every depth and hence to arbitrary countable mixtures."),
                Paragraph(Text("lengthProjection counts only the remaining Read letters. The two p atoms have masses sum nu(k) r(k) xi(k)^j and sum nu(k) (1-r(k))^2 xi(k)^j. The beta atoms at one, 2j+2 and 2j+3 have masses 1-mean(nu), sum nu(k) r(k)^2 xi(k)^j and sum nu(k) r(k)(1-r(k))^2 xi(k)^j, for every natural j, where xi(k)=r(k)(1-r(k)). The first atom lies in [1/3,2/5] for p and [3/5,2/3] for beta, so it separates the phases.")),
                Paragraph(Text("After phase separation, the odd p atoms or even beta atoms give all moments of eta(nu,e)=sum nu(k) r(k)^e dirac(xi(k)), with e=1 or e=2, on the compact interval [2/9,6/25]. Its total mass is at most one. The polynomial subalgebra separates this compact interval; MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish supplies finite-measure equality directly. Actual Fibonacci ratios and their xi values are injective, and positive finite singleton weights permit division to recover every posterior atom. No generic moment-determinacy claim or finite-support approximation is needed.")),
                Node("phase-posterior-laws", "posterior_phase_determine_both", "Phase and posterior determine both laws",
                    All("mu", Call("PMF", F.Id("PNat")), All("rho", Call("PMF", F.Id("PNat")),
                    All("h", Call("List", F.Id("Operation")), All("g", Call("List", F.Id("Operation")),
                    All("c", state, All("d", state, All("s", phase, All("t", phase,
                        Imp(Seq(domain, Land, Sp, statistics), Seq(laws, Land, Sp, transcripts)))))))))),
                    "The posterior length mixture supplies the first equality. The residual transport identity supplies the second, using the common phase and posterior. This step concerns distributions of the same source-permitted residual object."),
                Node("complete-recovery", "complete_original_recovery", "The three original law equivalences", recovery,
                    "Equality of length laws first gives phase and posterior equality through phase separation and compact moments. These statistics give equality of residual transcript laws. Conversely, the measurable transcriptCount selects the unique delivered budget and counts its Read operations; its actual pushforward is the length law, including none on the infinite return tail. These directions give all three displayed equivalences."),
                Paragraph(Text("Recovered depth means its conditional distribution, not zero-error identification of this run's hidden depth or prediction of its future realization. No posterior measurement port, physical elapsed-time identity, uniform cutoff, finite mean or extra delivery of past fields follows. The result is confined to the original active fourth-segment parser and its single unpaid Stop.")))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Imp(Formula p, Formula q) => Seq(Open, p, Close, Rightarrow, Open, q, Close);
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
