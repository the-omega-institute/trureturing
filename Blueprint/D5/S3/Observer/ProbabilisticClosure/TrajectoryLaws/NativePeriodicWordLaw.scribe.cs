using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativePeriodicWordLawDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePeriodicWordLaw.";

    public DocumentDefinition Create()
    {
        Formula t = F.Id("T"), s = F.Id("s"), z = F.Id("z"), n = F.Id("n");
        Formula b = F.Id("b"), c = F.Id("c"), i = F.Id("i"), x = F.Id("x");
        Formula word = Call("wordLaw", t, s, z);
        Formula finite = All(Equal(Call("realMass", word,
            Call("some", Call("typeWord", s, n, b))),
            Call("sourceCoord", t, s, n, b, Call("label", z))),
            ("n", "Nat"), ("b", "Letter"));
        Formula immediate = Imp(Equal(s, F.Id("beta")), Equal(
            Call("realMass", word, Call("singletonWord", D(1))),
            Seq(D(1), Minus, Call("v", t, Call("label", z)))));
        Formula identification = All(Imp(Call("activeConfig", z, s), And(finite, immediate)),
            ("T", "Parameters"), ("s", "ActivePhase"), ("z", "Config"));
        Formula normalized = All(Imp(Call("activeConfig", z, s), And(
            Equal(Call("mass", word, F.Id("univ")), D(1)),
            Equal(Call("mass", word, F.Id("none")), D(0)))),
            ("T", "Parameters"), ("s", "ActivePhase"), ("z", "Config"));
        Formula law = Call("fullLaw", Call("observer", t), Call("emitter", t),
            Call("configuration", c, i));
        Formula rendered = Call("fullRenderer", c, s, x);
        Formula box = Call("InBox", Call("realMass", law, rendered),
            Call("realMass", Call("endpointFull", F.Id("endpointA"), c), rendered),
            Call("realMass", Call("endpointFull", F.Id("endpointB"), c), rendered));
        Formula boxes = All(Imp(Call("activeNative", c, s), All(Bind("x", Call("ValidTail", s), box),
            ("i", "Label"))),
            ("c", "AcquiredNativeState"), ("s", "ActivePhase"));
        Formula fullNormalization = All(Imp(Call("activeNative", c, s), All(And(
            Equal(Call("mass", law, F.Id("univ")), D(1)),
            Equal(Call("mass", law, Call("fullRenderer", c, s, F.Id("none"))), D(0))),
            ("i", "Label"))), ("c", "AcquiredNativeState"), ("s", "ActivePhase"));
        Formula criterion = All(And(Seq(Open, boxes, Close, Leftrightarrow,
            Open, Call("Rates", t), Land, Call("ImmediateBoxes", t), Land,
            Call("Seeds", t), Close), fullNormalization), ("T", "Parameters"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact periodic endpoint boxes for native complete fourth-segment laws.",
            H("Periodic common generation on complete native carriers"), Blocks(
                Paragraph(Text("Parameters consists of a real w with 0<w<1/2 and two real emission vectors u,v on Label=Fin(3), each in the closed cube [1/3,2/5]^3. The initialization row is pi=(w,w,1-2w). Alpha acquired updates leave the label fixed, beta acquired updates swap labels 0 and 1 and fix label 2. These are A=I and B=((0,1,0),(1,0,0),(0,0,1)). Both actual acquisition and synthetic continuation use this one observer.update. Its public fields update by the original finiteStep; no alternate parser or renderer is introduced.")),
                Paragraph(Text("Config is the existing FiniteFields paired with the private label. observer initializes the original native fields with the probability row pi. At fourth p the emitter reads alpha with probability u_i; at fourth beta it reads alpha with probability v_i. Pending b emits the original matching Stop b, and delivered states emit padding. These laws are semantic probability measures for arbitrary admissible real parameters. No effective exact-real sampling assertion is required.")),
                Paragraph(Text("wordLaw(T,s,z) is the pushforward of the installed marked trajectory first by its existing rawFrom read stream and then by the existing stoppedReadWord(s). Its entire carrier is RawTail=Option(List(Letter)); none is the phase-specific infinite noncompletion outcome. The same installed generator has fullLaw on the original FullTranscript, with complete operation prefixes, held fields and event blocks.")),
                Paragraph(Text("Let H=diag(1-u) B diag(v) and g=diag(1-u) B (1-v). SourceCoord(T,p,n,0,i)=(H^n u)_i and sourceCoord(T,p,n,1,i)=(H^n g)_i; sourceCoord(T,beta,n,b,i)=v_i sourceCoord(T,p,n,b,i). typeWord(p,n,0)=(beta alpha)^n alpha, typeWord(p,n,1)=(beta alpha)^n beta beta, and typeWord(beta,n,b)=alpha typeWord(p,n,b). Letters alpha and beta have numeric codes 0 and 1.")),
                Paragraph(Text("In the formulas realMass(mu,x) means mu.real({x}), mass(mu,univ) means mu(univ), and mass(mu,x) for other x means mu({x}). singletonWord(1) denotes the immediate word [beta]. activeConfig(z,s) and activeNative(c,s) mean that the original finite control is fourth(active(s)); configuration(c,i) pairs c.source.finiteFields with i. ValidTail(s) includes none with its original validity proof.")),
                Node("native-periodic-identification", "native_word_identification",
                    "The generated native words have the source matrix coordinates", identification,
                    "The first marked-edge equation supplies the cylinder recursion. Its supported incoming mark and unchanged original finiteStep identify the head Read and its successor. Induction along the original pWord normal forms gives H^n u and H^n g; a suspended alpha returns by the same A=I update, while its immediate beta word has mass 1-v_i. The identification is derived from generation, with no correspondence premise."),
                Node("native-periodic-noncompletion", "native_noncompletion",
                    "Emission bounds alone eliminate native noncompletion mass", normalized,
                    "Every row of H has sum at most (4/15). The mass of the original loopWord(n) cylinder is the n-step survival iterate and is bounded by (4/15)^n. The parser's original noncompletion fibre lies in every such cylinder; in suspended phase it lies in the alpha-prefixed loop cylinders. Their uniform geometric bound tends to zero. The pushforward law is already an unconditional probability measure, so normalization does not rely on conditioning or on a supplied normalized Q or W."),
                Paragraph(Text("Write h_i=(1-u_i)v_(swap(i)), eta=h_0 h_1 and t=h_2. Rates(T) means (2/9)^2<=eta<=(6/25)^2 and 2/9<=t<=6/25. ImmediateBoxes(T) means 1-2/5<=1-v_i<=1-1/3 for every label. For r=1/3 and r=2/5, pureCoord(r,s,n,b)=(1 if s=p else r)(r if b=0 else (1-r)^2)[r(1-r)]^n. InBox(x,a,b) means min(a,b)<=x<=max(a,b). Seeds(T) requires sourceCoord(T,s,n,b,i) in these endpoint boxes for every phase, both word types, all labels and all n<=4.")),
                Paragraph(Text("endpointA and endpointB are exactly the existing parameters 1/3 and 2/5. endpointFull(r,c) is the original raw Bernoulli law pushed through fullTranscript(c), rather than a conditioned completion law. fullRenderer(c,s,x) renders each legal finite tail or the original infinite tail while retaining c's held record and literal event blocks. Its original readback is injective on ValidTail(s); singleton probabilities therefore transport without merging distinct native outcomes.")),
                Node("native-periodic-full-box", "native_full_box_criterion",
                    "Complete native endpoint boxes are equivalent to the finite criterion", criterion,
                    "The swap component satisfies H_*^2=eta I, and the fixed label multiplies by t. Necessity compares the strictly positive type-0 even subsequences with both endpoint rates; a rate outside either closed interval contradicts the unbounded powers of a quotient greater than one. The immediate suspended word supplies its bound, and restriction supplies every seed. For sufficiency, the two-step recurrence preserves ordered endpoint bounds. The type-0 order never switches, p type-1 switches at n=3, and suspended continuing type-1 switches at n=1. Tests through n=4 seed every required parity after the switch; strong induction supplies all n. Noncompletion has mass zero at both endpoints and for every emission table, independently of the rate and seed tests. The renderer transports every finite and both phase-specific infinite coordinates to the complete native transcript. Equality at the rate endpoints is included."),
                Paragraph(Text("These statements concern the periodic source-specific reversible common generator and its full native laws. They give neither an event-midpoint identity nor a total-variation attainment conclusion. The prior and update kernels remain those in the parameterized construction.")))));
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
    private static Formula Bind(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. xs]);
}
