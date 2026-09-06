using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class CompleteMediatorCutSharpBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.";
    private static Formula C => V("coupling");
    private static Formula N => V("law");
    private static Formula Y => V("table");
    private static Formula Best => V("best");
    private static Formula Zero => D(0);
    private static Formula One => D(1);
    private static Formula Half => Divide(One, D(2));
    private static Formula Lift => Call("completeOutcomeLaw", N);
    private static Formula Fair(Formula law) => Call("FairCompleteOutcome", law);
    private static Formula J(Formula law) => Call("completeMediatorBenefit", C, law);
    private static Formula Cut(Formula table) => Call("mediatorCutMass", C, table);
    private static Formula Comp => Lam("m", Call("not", Call("table", V("m"))));
    private static Formula PairLaw(Formula table) => Call("complementOutcomeLaw", table);
    private static Formula Mass(Formula law, Formula i) => Call("mass", law, i);
    private static Formula Bit(Formula table, Formula i) => Call("ite", Call("apply", table, i), One, Zero);
    private static Formula E(Formula coefficient, Formula law) => Call("linearObjective", coefficient, Call("mass", law));
    private static Formula Mean(Formula law, Formula m) => E(Lam("table", Bit(Y, m)), law);
    private static Formula Fst => Call("fst", V("pair"));
    private static Formula Snd => Call("snd", V("pair"));
    private static Formula Edge => Bin(Call("table", Fst), Neq, Call("table", Snd));
    private static Formula Event => And(Bin(Call("table", Fst), Eq, V("false")), Bin(Call("table", Snd), Eq, V("true")));
    private static Formula Assignment => E(Lam("pair", Call("ite", Event, One, Zero)), C);
    private static Formula Attains(Formula value) => Exist("law", And(Fair(N), Bin(J(N), Eq, value)));
    private static Formula Values => Call("setOf", Lam("value", Attains(V("value"))));
    private static Formula Maximal => All("table", Bin(Cut(Y), Le, Cut(Best)));
    private static Formula Separated => All("pair", Bin(Bin(Mass(C,V("pair")), Neq, Zero), Rightarrow, Edge));
    private static Formula Price => Call("completeMediatorPricingScore", C, V("multiplier"), Y);
    private static Formula Drift => Sum("pair", Bin(Mass(C,V("pair")), Cdot, Bin(Mean(N,Snd), Minus, Mean(N,Fst))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete mediation uses one response table in both treatment worlds. For a fixed mediator coupling, fair response marginals yield an exact weighted-cut interval and attaining independent-noise models.",
        H("Complete mediation, weighted cuts and exact pricing"),
        Blocks(
            Paragraph(Text("Mediator is an arbitrary finite type with decidable equality. coupling is an existing normalized nonnegative rational law on Mediator times Mediator; law is such a law on Mediator to Bool. table and best are complete Boolean response assignments, multiplier maps mediator states to rationals, and target is rational. All sums use the full finite carriers. The set Values displayed by setOf is the actual image of all fair laws under completeMediatorBenefit. The final two entries specialize Mediator to Fin 3.")),
            Describe.Lean(DescribeId.Create("complete-outcome-law"),
                DeclarationHandle.Create(Prefix + "completeOutcomeLaw"), H("Embed the no-direct-effect mechanism"),
                StatementSource.FromAuthor(Disp(All("Mediator law", Bin(Lift, Eq, Call("pushforwardResponseLaw", N, Lam("table", Lam("index", Call("table", Call("snd", V("index")))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both treatment coordinates read the same original response-table entry. This enforces equality of coordinates, rather than only equality of their means."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-outcome-law-success"),
                DeclarationHandle.Create(Prefix + "completeOutcomeLaw_success"), H("Recover the actual success kernel"),
                StatementSource.FromAuthor(Disp(All("Mediator law a m", Bin(Call("outcomeSuccess", Lift, V("a"), V("m")), Eq, Mean(N,V("m")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing pushforward expectation theorem identifies each intervention success probability."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fair-complete-outcome"),
                DeclarationHandle.Create(Prefix + "FairCompleteOutcome"), H("Fair response coordinates"),
                StatementSource.FromAuthor(Disp(All("Mediator law", Bin(Fair(N), Leftrightarrow, All("m", Bin(Mean(N,V("m")), Eq, Half)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each mediator-indexed outcome response has probability one half. Dependence between different coordinates remains unrestricted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-outcome-law-fair-kernel"),
                DeclarationHandle.Create(Prefix + "completeOutcomeLaw_fair_kernel"), H("Bind fairness to the mediator kernel API"),
                StatementSource.FromAuthor(Disp(All("Mediator law", Bin(Fair(N), Rightarrow, Call("HasOutcomeKernel", Lift, Lam("index", Half)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input condition is transported to the existing full treatment/mediator success-kernel predicate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-mediator-benefit"),
                DeclarationHandle.Create(Prefix + "completeMediatorBenefit"), H("Use the original independent source query"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling law", Bin(J(N), Eq, Call("partialMediatorBenefit", C, Lift))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mediator coupling stays fixed and the lifted outcome disturbance is combined with it by the existing product semantics."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-mediator-benefit-actual-response"),
                DeclarationHandle.Create(Prefix + "completeMediatorBenefit_actual_response"), H("Identify the actual benefit response cell"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling law", Bin(J(N), Eq, Call("benefitResponseMass", Call("mass", Call("partialMediatorResponseLaw", C, Lift))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The query is tied to the original two-world response pushforward and its existing benefit cell."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mediator-cut-mass"),
                DeclarationHandle.Create(Prefix + "mediatorCutMass"), H("Directed weight crossing a Boolean cut"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling table", Bin(Cut(Y), Eq, E(Lam("pair", Call("ite", Edge, One, Zero)), C))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each directed pair contributes its own weight. Symmetry is not assumed; loops never cross a cut."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-mediator-benefit-cut-identity"),
                DeclarationHandle.Create(Prefix + "completeMediatorBenefit_cut_identity"), H("Retain the complete mean-drift identity"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling law", Bin(Bin(D(2), Cdot, J(N)), Eq, Bin(E(Lam("table", Cut(Y)),N), Plus, Drift))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pointwise Boolean identity is averaged under the actual source law. Fairness is not needed for this identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-mediator-pricing-score"),
                DeclarationHandle.Create(Prefix + "completeMediatorPricingScore"), H("Actual outcome-column reduced cost"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling multiplier table", Bin(Price, Eq, Bin(Assignment, Minus, Sum("m", Bin(Call("multiplier",V("m")), Cdot, Bit(Y,V("m"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This subtracts the outcome-marginal dual terms from the actual deterministic benefit column. The separate constant normalization multiplier is omitted because it cannot affect the maximizing assignment."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-mediator-pricing-score-graph-identity"),
                DeclarationHandle.Create(Prefix + "completeMediatorPricingScore_graph_identity"), H("Expose cut plus vertex-field pricing"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling multiplier table", Bin(Bin(D(2), Cdot, Price), Eq, Bin(Cut(Y), Plus, Sum("m", Bin(Bin(Bin(Call("rightResponseMarginal",Call("mass",C),V("m")), Minus, Call("leftResponseMarginal",Call("mass",C),V("m"))), Minus, Bin(D(2), Cdot, Call("multiplier",V("m")))), Cdot, Bit(Y,V("m"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identity retains incoming and outgoing mediator masses and every rational dual multiplier. It is exact for arbitrary directed couplings and does not assert an efficient generic graph solver."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fair-complete-mediator-benefit-eq-half-cut"),
                DeclarationHandle.Create(Prefix + "fair_completeMediatorBenefit_eq_half_cut"), H("Cancel drift using the fair kernel"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling law", Bin(Fair(N), Rightarrow, Bin(J(N), Eq, Divide(E(Lam("table",Cut(Y)),N),D(2))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equal coordinate success probabilities cancel every signed mean difference, leaving half the expected weighted cut."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complement-outcome-law"),
                DeclarationHandle.Create(Prefix + "complementOutcomeLaw"), H("One fair disturbance selects an assignment or its complement"),
                StatementSource.FromAuthor(Disp(All("Mediator table", Bin(PairLaw(Y), Eq, Call("pushforwardResponseLaw", Call("uniformThresholdLaw",D(2)), Lam("bit", Call("ite", Bin(V("bit"), Eq, Zero), Y, Comp))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive-denominator proof is implicit in the displayed two-point uniform law. The same one-bit disturbance controls all response coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complement-outcome-law-fair"),
                DeclarationHandle.Create(Prefix + "complementOutcomeLaw_fair"), H("Simultaneous fairness of all coordinates"),
                StatementSource.FromAuthor(Disp(All("Mediator table", Fair(PairLaw(Y))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two complementary complete assignments jointly realize the prescribed success probability at every mediator value."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mediator-cut-mass-complement"),
                DeclarationHandle.Create(Prefix + "mediatorCutMass_complement"), H("Whole-table complementation preserves the cut"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling table", Bin(Cut(Comp), Eq, Cut(Y))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every edge has unchanged disagreement status after both endpoints are complemented."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complement-outcome-law-benefit"),
                DeclarationHandle.Create(Prefix + "complementOutcomeLaw_benefit"), H("Realize every deterministic cut value"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling table", Bin(J(PairLaw(Y)), Eq, Divide(Cut(Y),D(2)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual no-direct-effect model attains half the chosen cut mass, using one shared outcome disturbance independent of the mediator disturbance."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-mediator-maxcut-sharp"),
                DeclarationHandle.Create(Prefix + "complete_mediator_maxcut_sharp"), H("Obtain a maximizing cut and an attaining causal maximum"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling", Exist("best", And(Maximal, Call("IsGreatest",Values,Divide(Cut(Best),D(2)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite.exists_max chooses from the full Boolean assignment carrier. A complement pair attains the bound; every fair law is bounded by the maximum cut."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-mediator-cut-interval"),
                DeclarationHandle.Create(Prefix + "complete_mediator_cut_interval"), H("Exact image for every rational target"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling", Exist("best", And(Maximal, All("target", Bin(Attains(V("target")), Leftrightarrow, And(Bin(Zero,Le,V("target")),Bin(V("target"),Le,Divide(Cut(Best),D(2))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower witness uses two constant assignments. Mixing it with the maximizing complement law fills the entire interval within one outcome mechanism and leaves the mediator coupling unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mediator-cut-mass-eq-one-iff"),
                DeclarationHandle.Create(Prefix + "mediatorCutMass_eq_one_iff"), H("Full cut mass is a simultaneous support condition"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling table", Bin(Bin(Cut(Y),Eq,One), Leftrightarrow, Separated)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative missed-edge masses sum to zero exactly when no positive mediator pair remains unseparated."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-mediator-half-attainable-iff"),
                DeclarationHandle.Create(Prefix + "complete_mediator_half_attainable_iff"), H("Characterize saturation by a single two-coloring"),
                StatementSource.FromAuthor(Disp(All("Mediator coupling", Bin(Attains(Half), Leftrightarrow, Exist("table",Separated))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is a full iff on the positive directed-pair support. It treats loops and odd cycles through the actual Boolean separation condition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-cycle-coupling"),
                DeclarationHandle.Create(Prefix + "threeCycleCoupling"), H("Normalized directed three-cycle instance"),
                StatementSource.FromAuthor(Disp(All("pair", Bin(Mass(Call("threeCycleCoupling"),V("pair")), Eq, Call("ite", Or(Bin(V("pair"),Eq,Call("pair",D(0),D(1))),Bin(V("pair"),Eq,Call("pair",D(1),D(2))),Bin(V("pair"),Eq,Call("pair",D(2),D(0)))),Divide(One,D(3)),Zero))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete mediator law has three equally weighted directed edges. The source supplies nonnegativity and normalization, with no estimated edge weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("three-cycle-complete-mediation-sharp"),
                DeclarationHandle.Create(Prefix + "three_cycle_complete_mediation_sharp"), H("Exact one-third endpoint on the odd cycle"),
                StatementSource.FromAuthor(Disp(Call("IsGreatest", Call("setOf",Lam("value",Exist("law",And(Fair(N),Bin(Call("completeMediatorBenefit",Call("threeCycleCoupling"),N),Eq,V("value")))))), Divide(One,D(3))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every Boolean labeling cuts at most two of the three cycle edges. The assignment 001 and its complement give an actual fair attaining outcome law. The cellwise half bound is therefore strictly loose."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Bin(Formula a, Formula op, Formula b) => Seq(Par(a), Sp, op, Sp, Par(b));
    private static Formula Divide(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Lam(string name, Formula body) => Par(Seq(LambdaLower, Sp, V(name), Sp, Mapsto, Sp, body));
    private static Formula Sum(string index, Formula body) => Seq(F.Sum, Underscore, Grp(V(index)), Sp, Par(body));
    private static Formula And(params Formula[] clauses) => Join(Land, clauses);
    private static Formula Or(params Formula[] clauses) => Join(Lor, clauses);
    private static Formula Join(Formula op, Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i) result = Bin(clauses[i], op, result);
        return result;
    }
    private static Formula All(string names, Formula body) => Quant(Forall, names, body);
    private static Formula Exist(string names, Formula body) => Quant(Exists, names, body);
    private static Formula Quant(Formula q, string names, Formula body)
    {
        var parts = new List<Formula> { q, Sp };
        foreach (var name in names.Split(' ')) parts.AddRange([V(name), Comma, Sp]);
        parts.Add(body);
        return Seq([.. parts]);
    }
    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < arguments.Length; ++i)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(arguments[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
}
