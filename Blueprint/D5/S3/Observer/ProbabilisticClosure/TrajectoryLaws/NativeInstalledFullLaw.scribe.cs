using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeInstalledFullLawDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.";

    public DocumentDefinition Create()
    {
        Formula m = F.Id("M"), e = F.Id("e"), z = F.Id("z"), x = F.Id("x");
        Formula c = F.Id("c"), s = F.Id("s"), op = F.Id("op"), fp = F.Id("fprime");
        Formula ev = F.Id("E"), b = F.Id("b"), mu = F.Id("mu");
        Formula law = Call("fullLaw", m, e, z), fields = Call("project", m, z);
        Formula realization = All(Imp(Call("Coherent", m, x),
            All(Imp(Equal(Call("fields", c), Call("projectAtZero", m, x)),
                Equal(Call("markedTranscript", m, x),
                    Call("fullTranscript", c, Call("rawFrom", x)))),
                ("c", "AcquiredNativeState"))), ("x", "MarkedPathZ"));
        Formula identity = All(Imp(And(Equal(fields, Call("fields", c)),
            Equal(Call("control", Call("fields", c)), Call("fourthActive", s))),
            Equal(law, Call("map", Call("tailLaw", m, e, s, z),
                Call("fullRenderer", c, s)))),
            ("s", "ActivePhase"), ("z", "Z"), ("c", "AcquiredNativeState"));
        Formula recursion = All(Imp(Equal(Call("finiteStep", fields, op), Call("some", fp)),
            All(Imp(Call("MeasurableSet", ev),
                Equal(Call("mass", law, Call("blockEvent", fields, fp, op, ev)),
                    Seq(Call("emissionMass", e, z, Call("some", op)), Cdot,
                        Call("weightedSuccessorMass", m, e, z, op, ev)))),
                ("E", "SetFullTranscript"))),
            ("z", "Z"), ("op", "Operation"), ("fprime", "FiniteFields"));
        Formula normalization = All(Call("IsProbabilityMeasure", law), ("z", "Z"));
        Formula support = All(Call("AlmostSureNative", m, e, z), ("z", "Z"));
        Formula pending = All(Imp(Equal(Call("control", fields), Call("pending", b)),
            Equal(Call("emit", e, z), Call("pure", Call("some", Call("stop", b))))),
            ("z", "Z"), ("b", "Letter"));
        Formula terminal = All(Imp(Equal(Call("control", fields), Call("delivered")),
            Equal(law, Call("dirac", Call("terminalTranscript", fields)))), ("z", "Z"));
        Formula risk = All(Equal(Call("installedRisk", m, e, mu, s),
            Call("rawRisk", m, mu, s, Call("HistoryIndependentTailLaw", m, e, s))),
            ("mu", "PMFDepth"), ("s", "ActivePhase"));
        Formula complete = And(normalization, And(support,
            And(recursion, And(pending, And(terminal, risk)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Installed configuration laws with literal native event blocks.",
            H("The installed generator and its complete trajectory"), Blocks(
                Paragraph(Text("Z is the original finite COMPLETE configuration carrier, with Fintype, MeasurableSpace and MeasurableSingletonClass. Observer M is unchanged: project reads the original FiniteFields and update(op,z) is its original source-independent probability row. init is used for actual acquired histories; it is never resampled in a synthetic residual law. InstalledEmitter e adds a semantic PMF emit(z) on Option Operation. Its supported some(op) must be lawful under finiteStep(project(z),op), and supported none requires delivered control. Hence seed, early and fourth active states emit Reads, pending(b) emits its matching Stop surely, and delivered emits none surely. The law may depend on every component of Z. These are semantics of a charged installed program, without an executable realization assertion for arbitrary real probability tables.")),
                Paragraph(Text("MarkedPathZ means a stream of pairs in W=Z times Option Operation. W is an analysis carrier, not additional COMPLETE memory. markedRow(M,e,(z,a)) samples emit(z), then for some(op) samples exactly M.update(op,z) and records (zprime,some(op)). For none it preserves z and records (z,none). markedKernel is this PMF as a Markov kernel. markedLaw starts from the delta at (z,none) and uses Mathlib Kernel.trajMeasure; its first-edge decomposition is a measure equality on the entire infinite trajectory. The frozen MarkovPrefixMass singleton-prefix formula identifies its finite-dimensional measures, and projective uniqueness extends the decomposition to all measurable path events. No conditional row or division by an emission probability is used.")),
                Paragraph(Text("operations(x,n) collects incoming marks at coordinates 1 through n; coordinate 0 is ignored. Its value is none after the first padding mark. markedTranscript(M,x)(n) records these operation prefixes, M.project(x(n).first), and eventBlocks generated from the initial projected fields. rawFrom(x)(i) reads the Read letter from the incoming mark at i+1, using a dummy alpha for Stop or padding. On a coherent trajectory all Reads precede Stop, so the dummy letters occur only where the native delivered parser cannot read them. representative(f) supplies the fields f with zero analysis counts and zero payloadReturns. Those counters do not enter the full output.")),
                Paragraph(Text("Coherent(M,x) means that every Edge(M,x(n),x(n+1)) holds. A some(op) edge projects to exactly finiteStep; a none edge starts at delivered and preserves the same private configuration. AlmostSureNative(M,e,z) means that for almost every x under markedLaw(M,e,(z,none)), markedTranscript(M,x)=fullTranscript(representative(project(M,z)),rawFrom(x)). The PMF support of every trajectory edge gives coherence simultaneously for all natural event indices. Full native execution retains paid seed rejection, both accepted seeds, every marker triple, arbitrary payload returns, current registers and the Stop transaction. The completion event list writes before latching and preserves the complete held records.")),
            Node("native-installed-realization", "marked_native_realization",
                "The marked decoder is the original native execution", Universal(realization, false),
                "For every coherent infinite marked trajectory and every acquired native state with the same initial finite fields, the two full transcripts coincide at every cut. The construction follows the incoming Read letters and the projected actual update edges. A matching Stop performs its native update and entire event block; the following padding produces none. No eventual completion, irreducibility or positivity of each transition is assumed."),
                Paragraph(Text("fullLaw(M,e,z) is the pushforward of markedLaw(M,e,(z,none)) by markedTranscript(M). It is a normalized probability measure on FullTranscript. It has no history, prior, posterior, latent depth or clock argument. Infinite noncompletion is part of this probability space. In particular distinct infinite seed-rejection streams retain their different operation prefixes; none is not a global compression of seed noncompletion. Equality for native states with identical finite fields uses drive_control, drive_spec and the original execute_finite_projection. These deterministic results identify finite fields and event blocks without imposing constraints on the analysis counters.")),
                Paragraph(Text("For an active fourth phase s, tailValue(s,omega) is stoppedReadWord(s,omega) with its WordFamily validity proof. tailLaw(M,e,s,z) is its pushforward from the same marked trajectory via rawFrom. ValidTail(s) contains the legal finite fourth words and their unique infinite noncompletion word. This fourth-only none outcome does not collapse the complete seed parser. Both fullLaw and tailLaw are probability measures even at emission endpoints and when fourth noncompletion has mass one. For scalar return data A=B=1,u=0,v=1, the infinite trajectory is retained; no resolvent or eventual-completion hypothesis enters.")),
            Node("native-installed-configuration", "installed_configuration_identity",
                "A configuration law renders the full fourth future", Universal(identity, true),
                "Whenever project(M,z)=c.source.finiteFields and c is fourth-active(s), fullLaw(M,e,z) is the image of tailLaw(M,e,s,z) under fullRenderer(c,s). The same z determines the complete law on both sides. The identity follows from actual marked realization, deterministic finite-fields factorization and full_renderer_all_paths. It preserves every original operation, finite held field and literal event block."),
                Paragraph(Text("blockEvent(f,fprime,op,E) is the measurable set of transcripts t satisfying t(0)=some([],f,[]), t(1)=some([op],fprime,[eventBlock(f,op)]), and deleteBlock(t) in E. DeleteBlock removes one operation and its entire original block. weightedSuccessorMass(M,e,z,op,E) denotes the finite sum over zprime in Z of M.update(op,z)(zprime) times fullLaw(M,e,zprime)(E). emissionMass(e,z,some(op)) is e.emit(z)(some(op)). These rows are bound before synthesis and remain the literal original rows at zero emission.")),
            Node("native-installed-recursion", "installed_first_block_recursion",
                "Exact first-block recursion", Universal(recursion, true),
                "For every lawful finiteStep and every measurable full residual event, the block-event mass equals the emission mass times the original-update average of successor full laws. The unconditional trajectory decomposition is applied before decoding; the first native block and its entire deleted suffix are identified on supported paths. This proves the equation for arbitrary measurable E, including noncompletion events, without a positivity premise on the emission."),
                Paragraph(Text("terminalTranscript(f) has coordinate 0 equal to some([],f,[]) and every later coordinate none. pending(b) and delivered in the formulas mean the corresponding fourth controls. installedRisk(M,e,mu,s) is the supremum over every PhaseHistory(s) of the actual row-weighted measurable total variation between fullLaw(M,e,z) and fullTarget(M,mu,h,c). HistoryIndependentTailLaw denotes the family (H,z) mapped to tailLaw(M,e,s,z); AlmostSureNative is the path equality defined above. PMFDepth includes all finite or countable positive-integer priors. The source keeps one common latent K; no endpoint mass assumption is needed for this transport identity.")),
            Node("native-installed-law", "installed_full_law",
                "One installed law supplies generation and history risk transport", Universal(complete, true),
                "The six conjuncts give full-law normalization, almost-sure literal native realization, exact arbitrary-event recursion, forced pending Stop emission, the delivered Dirac law, and equality of installed configuration-before-TV risk with rawRisk for the history-independent tail family. The risk proof uses actual_row_refines at every original PhaseHistory and native_history_risk_transport. Zero-weight configurations contribute zero; supported configurations satisfy the full renderer identity. This includes all positive finite paid seed histories and all fourth returns, rather than only the first fourth p cut."),
                Paragraph(Text("Definitions 1.1 and 1.2 supply the same-depth source, complete original fields and literal event renderer. Definition 1.3 supplies the finite COMPLETE carrier and its installed semantic emissions and source-independent updates; the first-block theorem gives its exact generation equation for the constructed D laws. The configuration identity makes the tail family history-independent and applies the existing full-history risk transport to those constructed laws. Definition 1.4 still requires the designated seed-1, marker-100 fibre and constant suspended alpha emission there; it asserts no equality of suspended laws or update rows.")),
                Paragraph(Text("The original strict bound e(M)>1/195200 is not a conclusion of these statements. Its remaining connections are bounded ENNReal-to-real risk and excess conversion, extraction of common actual stationary rows for countable priors, normalized clipping with its distortion bound, and application of ConstantSuspensionSeparator on the resulting regular table. The constant-emission condition must be transported on the designated reachable fibre. No unrestricted-observer gap or free exact-real sampling assertion follows.")),
                Node("marked-prepend-measurable", "measurable_prepend", "Prepending a marked head is measurable",
                    All(Call("MeasurablePrepend", F.Id("a")), ("A", "MeasurableType"), ("a", "A")),
                    "For every measurable carrier A and a in A, prepend(a) on infinite A paths is measurable. Its zero coordinate is constant and each successor coordinate is the corresponding original path coordinate."),
                Node("marked-regenerate", "marked_regenerate", "The original complete marked regeneration law",
                    Universal(All(Call("MarkedRegenerate", m, e, F.Id("w")), ("w", "MarkedZ")), true),
                    "For every original finite measurable singleton carrier Z, observer M, lawful InstalledEmitter e and incoming marked state w, markedLaw(M,e,w) equals the finite sum over v of markedRow(M,e,w,v) times the pushforward of markedLaw(M,e,v) under prepend(w). This is an equality of complete infinite-path measures. The original singleton-prefix calculation and projective uniqueness provide it without completion or positive-emission assumptions."),
                Node("raw-from-measurable", "rawFrom_measurable", "The marked read projection is measurable",
                    All(Call("RawFromMeasurable", F.Id("Z")), ("Z", "FiniteMeasurableSingletonType")),
                    "The map rawFrom from infinite marked Z paths to binary streams is measurable on the original finite measurable singleton carrier. Coordinate n reads the incoming mark at n+1 and uses zero for marks that are not Reads."),
                Node("marked-head", "marked_head", "The marked initial head holds almost surely",
                    Universal(All(Call("MarkedHead", m, e, F.Id("w")), ("w", "MarkedZ")), true),
                    "For every M, lawful e and marked initial state w, almost every path under markedLaw(M,e,w) has coordinate zero equal to w. Incoming-mark invariance and prefixed read pushforwards use this actual path identity."),
                Node("marked-some-mass", "marked_some_mass", "The marked acquired operation uses the original kernel",
                    Universal(All(Call("MarkedSomeMass", m, e, z, F.Id("zprime"), op),
                        ("z", "Z"), ("zprime", "Z"), ("op", "Operation")), true),
                    "For every original configurations z,zprime and operation op, markedRow(M,e,(z,none),(zprime,some(op))) equals e.emit(z)(some(op)) times M.update(op,z)(zprime). The original update is used even when the emission has zero mass."))));
    }

    private static Formula Universal(Formula body, bool emitter)
    {
        if (emitter) body = All(body, ("e", "InstalledEmitterM"));
        return All(Imp(Call("FiniteMeasurableSingleton", F.Id("Z")),
            All(body, ("M", "ObserverZ"))), ("Z", "Type"));
    }
    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Land, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Rightarrow, Open, b, Close);
    private static Formula All(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(xs[i].Name), Colon, F.Id(xs[i].Type), Comma, Sp,
                Open, body, Close);
        return body;
    }
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Call(string name, params Formula[] xs)
    {
        Formula result = Seq(Operatorname, Grp(F.Id(name)), Open);
        for (var i = 0; i < xs.Length; i++)
            result = i == 0 ? Seq(result, xs[i]) : Seq(result, Comma, Sp, xs[i]);
        return Seq(result, Close);
    }
}
