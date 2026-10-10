using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeObserverJointLawDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.";

    public DocumentDefinition Create()
    {
        Formula m = F.Id("M"), mu = F.Id("mu"), h = F.Id("h"), c = F.Id("c");
        Formula k = F.Id("k"), z = F.Id("z"), e = F.Id("E"), s = F.Id("s");
        Formula op = F.Id("op"), nf = F.Id("nf"), Hh = F.Id("H"), d = F.Id("D");
        Formula legal = Equal(Call("run", h), Call("some", c));
        Formula row = Call("row", m, h);
        Formula condition = Call("cond", Call("actualLaw", m, mu, Call("length", h)),
            Call("historyCut", h, c));
        Formula source = Call("cond", Call("jointLaw", mu), Call("nativeEvent", h, c));
        Formula posterior = Call("posterior", mu, h, c);
        Formula factor = All(Imp(legal, All(Imp(Call("MeasurableSet", e),
            Equal(Call("mass", Call("actualLaw", m, mu, Call("length", h)),
                Call("taggedHistory", h, c, k, e), Call("singleton", z)),
                Product(Call("at", mu, k), Call("likelihood", h, k),
                    Call("at", row, z), Call("mass", Call("rawReadLaw", Call("rate", k)), e)))),
            ("k", "Depth"), ("z", "Z"), ("E", "SetStream"))),
            ("h", "ListOperation"), ("c", "AcquiredNativeState"));
        Formula conditional = All(Imp(legal, Equal(condition,
            Call("prod", source, Call("toMeasure", row)))),
            ("h", "ListOperation"), ("c", "AcquiredNativeState"));
        Formula sameK = All(Imp(legal, Equal(Call("map", condition, Call("sameKShift", h)),
            Call("prod", Call("jointLaw", posterior), Call("toMeasure", row)))),
            ("h", "ListOperation"), ("c", "AcquiredNativeState"));
        Formula projection = All(Imp(Call("inSupport", z, row),
            Equal(Call("project", m, z), Call("fields", c))), ("z", "Z"));
        Formula updates = All(Equal(Call("row", m, Call("append", h, Call("singletonList", op))),
            Call("bind", row, Call("update", m, op))), ("op", "Operation"));
        Formula form = Seq(Exists, Sp, nf, Colon, F.Id("PrefixForm"), Comma, Sp,
            Open, And(Equal(Call("render", nf), h), And(Equal(c, Call("reconstruct", nf)),
                Call("PrefixFacts", nf, c))), Close);
        Formula refinement = All(Imp(legal, And(projection, And(updates, form))),
            ("h", "ListOperation"), ("c", "AcquiredNativeState"));
        Formula risk = And(All(Call("CutEvidence", m, mu, s, Hh), ("H", "PhaseHistory")),
            Equal(Call("fullRisk", m, mu, s, d), Call("rawRisk", m, mu, s, d)));
        risk = All(risk, ("s", "ActivePhase"), ("D", "LawfulDecoderFamily"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Ordered acquired observer rows and the same-source full history law.",
            H("The constructed actual law"), Blocks(
                Paragraph(Text("Every statement is universal in a type Z with Fintype, MeasurableSpace and MeasurableSingletonClass, an Observer M on Z and an arbitrary probability mass function mu on positive integer Depth. Z is the one finite COMPLETE carrier. M.project reads the original FiniteFields; initialization has support over the original initial fields. M.update(op,z) is a fixed source-independent PMF on Z. Each supported successor projects to finiteStep when that original operation is lawful. There is no depth, history, posterior, readable distribution, clock or paid counter argument in M. Numerical representation, selectors, workspace and all persistent random state must belong to this finite carrier in any implementation mapped to the interface.")),
                Paragraph(Text("advance applies the acquired kernels by recursive PMF.bind in the actual operation order, and row(M,h)=advance(M,M.init,h). Equal letter counts determine source likelihoods, not these ordered products. cutHistory reads the successful native operation prefix at an event cut and saturates after delivered Stop. privateKernel(M,n)(k,omega) is the measure of row(M,cutHistory(omega,n)). actualLaw is jointLaw(mu) composed with this explicitly constructed Markov kernel. This is a probability measure, not an arbitrary joint-law field. The source draws one K and supplies every seed and payload Read conditional independently at rate(K). Analysis histories, counts and rows are not runtime data.")),
                Paragraph(Text("ListOperation means List Operation, SetStream means Set Stream, and fields(c)=c.source.finiteFields. mass(L,A,{z}) is L(A times {z}); mass(L,E) is L(E). historyCut(h,c)=nativeEvent(h,c) times the whole Z carrier. taggedHistory(h,c,k,E) is the intersection of nativeEvent(h,c) with the set of (K,omega) satisfying K=k and rawTail(omega,length(readLetters(h))) in E. Deterministic original events add no likelihood. Every legal h has a positive normalizer under every installed PMF; neither paid rejections, partial parses nor fourth returns are excluded.")),
                Node("ordered-history-factorization", "ordered_history_factorization", "Full ordered history factorization",
                    Universal(factor, true), "For every original legal history, every source depth, every configuration and every measurable unread-source event, the joint mass factors as mu(k) times its original acquired-word likelihood times the ordered private row times the same-depth unread-source law. The kernel is constant on the exact native history cylinder. Prefix-tail independence is used at that same depth. No future-event condition or reset is introduced."),
                Node("conditional-history-product", "conditional_history_product", "Conditional source and private row",
                    Universal(conditional, true), "After conditioning on the full native history, the joint source/private measure is the product of the conditional original source measure and the entire ordered row. All configurations remain in the conditional law, including rows that can occur only at earlier transient histories."),
                Node("same-k-private-tail", "sameK_private_tail", "Retain K while deleting acquired Reads",
                    Universal(sameK, true), "sameKShift(h) maps ((k,omega),z) to ((k,rawTail(omega,length(readLetters(h)))),z). The unread source is jointLaw of the original posterior and the private row is unchanged. K is retained literally. This supplier is used in the full target transport proof."),
                Node("actual-row-refines", "actual_row_refines", "Full native state at every acquired row",
                    Universal(refinement, false), "Every positive row configuration has the actual native fields. Appending any operation composes the same acquired update even if a separate synthetic emission gives it zero probability. A legal history also has its original PrefixForm witness, with full reconstruction and PrefixFacts. Both seeds, every accepted or rejected paid pair, all marker branches and unbounded return counts remain covered by this original grammar."),
                Paragraph(Text("validStopped(s,omega) pairs stoppedReadWord with its WordFamily witness, or with the unique infinite noncompletion outcome. rawTarget(mu,h,c,s) is the conditional original source mapped to validStopped on its unread tail. fullTarget(M,mu,h,c) is the conditional actual source/private law mapped to the full native transcript of that same tail. The valid carrier retains old synthetic noncompletion; the actual posterior mixture has the original homogeneous stopped-word masses. No clipped law is constructed here.")),
                Paragraph(Text("PhaseHistory(s) consists of every pair H=(h,c) with run(h)=some(c) and c in fourth active phase s. It has no length or rejection bound. LawfulDecoderFamily means a function D assigning to each such H and configuration z a measure on ValidTail(s); it is a separately supplied decoded law, not a constructed generator. fullRisk is the supremum over this entire history type of the finite sum row(M,h)(z) times TV of the rendered D(H,z) and fullTarget. rawRisk uses D(H,z) and rawTarget in the same order. TV is the canonical ENNReal event-supremum measurableTotalVariation. In particular the averaging occurs after TV, before the history supremum.")),
                Paragraph(Text("CutEvidence(M,mu,s,H), for H=(h,c), is the conjunction of: rawTarget and fullTarget are probability measures; fullTarget=(fullRenderer(c,s))_*rawTarget; (Subtype.val)_*rawTarget=wordMixture(posterior(mu,h,c),s); the conditional actual private marginal equals row(M,h).toMeasure; the positive configuration projection; the ordered append-update equality; and the PrefixForm reconstruction in actual_row_refines. It includes the full ordered tagged-history mass factorization for every k, z and measurable unread E, with the same formula as ordered_history_factorization at H. It also includes both full event obligations: for every raw omega and lawful nextNative(c,omega)=(op,d), deleting one operation and its whole event block from fullTranscript(c,omega) equals fullTranscript(d,rawTail(omega,readCost(op))); and for every omega in the acquired readLetters(h) cylinder, the initial full transcript at length(h) contains h, fields(c) and all original blocks, whose replay reconstructs fields(c) and originalView(c). These are all original theorem conjuncts, not additional assumptions.")),
                Node("native-history-risk-transport", "native_history_risk_transport", "Actual full target and all-history risk transport",
                    Universal(risk, true), "The full target is proved equal to the rendered constructed raw target, with its posterior stopped-word mixture. The entire actual conditional row and original event reconstruction are transported. Two measurable inverses preserve each configuration distance, so the original full-history supremum equals the raw supremum. The original source likelihood uses all acquired Reads. The law, row and field clauses are live consumers of the renderer, same-K and native reconstruction results."),
                Paragraph(Text("This bridge concerns the exact native source and source-independent finite acquired updates. It does not construct an arbitrary observer's synthetic decoded generator or establish its exact generation equation, a counted realization theorem, common stationary actual rows, endpoint concentration, normalized clipped laws or clipping distortion. Those connections remain required before applying the regular-table separator to the original observer lower bound. No conclusion of the strict 1/195200 bound is asserted here.")))));
    }

    private static Formula Universal(Formula body, bool prior)
    {
        if (prior) body = All(body, ("mu", "PMFDepth"));
        return All(Imp(Call("FiniteMeasurableSingleton", F.Id("Z")),
            All(body, ("M", "ObserverZ"))), ("Z", "Type"));
    }
    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Land, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Rightarrow, Open, b, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Product(params Formula[] xs)
    {
        Formula result = xs[0];
        for (var i = 1; i < xs.Length; i++) result = Seq(result, Cdot, xs[i]);
        return result;
    }
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
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
