using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class MarkerPermutationActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.";
    private static Formula I(string s) => F.Id(s);
    private static Formula.BoundVariable B(string n, Formula t) =>
        new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] bs) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. bs], f);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Fn(Formula a, Formula b) => Call("Function", a, b);
    private static Formula At(Formula f, Formula a) => Call("apply", f, a);
    private static Formula Typed(Formula f, Formula t) => Seq(f, Colon, t);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Perm => Call("Perm", I("I"));
    private static Formula SeqType => Fn(I("Int"), I("E"));
    private static Formula WordType(Formula n) => Fn(Call("Fin", n), I("E"));
    private static Formula WType => Call("GuardedWords", I("E"), I("I"), I("m"), I("d"));
    private static Formula Marker => Call("marker", I("W"));
    private static Formula Data => Call("data", I("W"));
    private static Formula Occ(Formula x, Formula a) => Call("Occurs", I("W"), x, a);
    private static Formula Sel(Formula x, Formula a, Formula i) =>
        Call("Selected", I("W"), x, a, i);
    private static Formula Rep(Formula pi, Formula x) => Call("replace", I("W"), pi, x);
    private static Formula Inv(Formula pi) => new Formula.Power(pi, Seq(Minus, Num(1)));
    private static Formula J => Call("integerIndex", I("j"));
    private static Formula Radius => Add(I("m"), I("d"));
    private static Formula Base(Formula f, params Formula.BoundVariable[] extra) => All(f,
        [B("E", I("Type")), B("I", I("Type")), B("m", I("Nat")), B("d", I("Nat")),
         B("W", WType), .. extra]);
    private static Formula LoopScope(Formula f, bool topological, bool finite,
        params Formula.BoundVariable[] extra)
    {
        var bs = new List<Formula.BoundVariable> {
            B("V", I("Type")), B("G", Call("DirectedMultigraph", I("V"), I("E"))),
            B("p", I("V")), B("L", Call("Loops", I("W"), I("G"), I("p"))) };
        if (topological)
            bs.AddRange([B("topE", Call("TopologicalSpace", I("E"))),
                B("discreteE", Call("DiscreteTopology", I("E")))]);
        if (finite)
            bs.AddRange([B("finV", Call("Fintype", I("V"))),
                B("finE", Call("Fintype", I("E"))), B("eqV", Call("DecidableEq", I("V"))),
                B("topV", Call("TopologicalSpace", I("V"))),
                B("discreteV", Call("DiscreteTopology", I("V")))]);
        bs.AddRange(extra);
        return Base(f, [.. bs]);
    }
    private static Formula Graph => Call("expandedGraph", Call("resetMatrix", I("q")));
    private static Formula Edges => Call("Product", Call("Edge", Call("resetMatrix", I("q"))),
        I("MultiplicativeBool"));
    private static Formula M => Add(Mul(Num(6), I("k")), Num(5));
    private static Formula Dlen => Mul(Num(6), I("k"));
    private static Formula Bits => Fn(Call("Fin", I("k")), I("Bool"));
    private static Formula ResetScope(Formula f, bool positiveK,
        params Formula.BoundVariable[] extra) => All(f,
        [B("q", I("Nat")), B("k", I("Nat")), B("hq", Lt(Num(1), I("q"))),
         .. (positiveK ? new[] { B("hk", Lt(Num(0), I("k"))) } : []), .. extra]);
    private static Formula Action => Call("action", I("W"), I("G"), I("L"));

    public DocumentDefinition Create()
    {
        var entries = new List<DocumentBlock>();
        void Entry(string name, string title, Formula f, string prose, bool definition = false) =>
            entries.Add(Describe.Lean(DescribeId.Create(name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
                DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title),
                StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(prose))),
                definition ? DescribeRole.Definition : DescribeRole.Theorem));
        Entry("Guarded.NoPartialOverlap", "Unbordered at every edge offset",
            All(Typed(Call("NoPartialOverlap", I("M")), I("Prop")),
                B("E", I("Type")), B("m", I("Nat")), B("M", WordType(I("m")))),
            "NoPartialOverlap M means that for every natural r with 0<r<m, the equality "
            + "M[r+j]=M[j] fails for at least one j in Fin(m-r). The indices retain their "
            + "proved bounds. No return-time alignment or symbolic conjugacy is assumed.", true);
        Entry("Guarded.Words", "Finite marker and injective data family",
            All(Typed(WType, I("Type")), B("E", I("Type")), B("I", I("Type")),
                B("m", I("Nat")), B("d", I("Nat"))),
            "Words stores marker:Fin m→E and data:I→Fin d→E, with 0<m, d<m, "
            + "NoPartialOverlap marker and Function.Injective data. E and I may have "
            + "independent universes. These are finite-word hypotheses, not a marker automorphism.", true);
        Entry("Guarded.Occurs", "Exact integer marker occurrence",
            Base(Iff(Occ(I("x"), I("a")), All(Equal(At(I("x"), Add(I("a"), J)),
                At(Marker, I("j"))), B("j", Call("Fin", I("m"))))),
                B("x", SeqType), B("a", I("Int"))),
            "Function(A,B) is the full function type A→B; apply is evaluation. integerIndex(j) "
            + "casts the natural value of j to Int. Occurs compares every original edge.", true);
        Entry("Guarded.Selected", "A guarded data interval",
            Base(Iff(Sel(I("x"), I("a"), I("i")),
                And(Occ(I("x"), I("a")), And(Occ(I("x"), Add(Add(I("a"), I("m")), I("d"))),
                    All(Equal(At(I("x"), Add(Add(I("a"), I("m")), J)),
                        At(At(Data, I("i")), I("j"))), B("j", Call("Fin", I("d"))))))),
                B("x", SeqType), B("a", I("Int")), B("i", I("I"))),
            "Selected W x a i is exactly M D_i M starting at a. Natural lengths are cast "
            + "to Int in coordinate sums. Only the half-open central interval is replaceable.", true);
        Entry("Guarded.replace", "Simultaneous central-data replacement",
            Base(Typed(At(Rep(I("pi"), I("x")), I("t")), I("E")),
                B("pi", Perm), B("x", SeqType), B("t", I("Int"))),
            "At a coordinate in a selected gap, replace outputs data(pi(i)) at the same "
            + "offset. Otherwise it returns x(t). Marker separation proves unique start, "
            + "injective data proves unique label, and coordinate equality proves unique offset. "
            + "The noncomputable selection changes no mathematical choice of output.", true);
        Entry("Guarded.marker_occurrences_invariant", "Every marker occurrence is invariant",
            Base(Iff(Occ(Rep(I("pi"), I("x")), I("a")), Occ(I("x"), I("a"))),
                B("pi", Perm), B("x", SeqType), B("a", I("Int"))),
            "Distinct unbordered markers are at least m apart. A marker of length m>d "
            + "meeting a selected gap must overlap one of its protected guards. This proves "
            + "both preservation and exclusion of new markers on arbitrary bilateral sequences. "
            + "It is used by eligibility invariance, inverse and composition.");
        Entry("Guarded.selected_iff", "Eligibility and data labels are preserved",
            Base(Iff(Sel(Rep(I("pi"), I("x")), I("a"), At(I("pi"), I("i"))),
                Sel(I("x"), I("a"), I("i"))),
                B("pi", Perm), B("x", SeqType), B("a", I("Int")), B("i", I("I"))),
            "Exactly the same selected intervals survive. The data label becomes pi(i). "
            + "A previously unselected interval cannot become eligible because any hit there "
            + "would already have the same selected start. This supports the real group law.");
        Entry("Guarded.replace_mul", "Ordinary permutation composition",
            Base(Equal(Rep(I("pi"), Rep(I("tau"), I("x"))),
                Rep(Mul(I("pi"), I("tau")), I("x"))),
                B("pi", Perm), B("tau", Perm), B("x", SeqType)),
            "The convention is (pi*tau)(i)=pi(tau(i)). All successive replacements use "
            + "the same intervals, including adjacent templates sharing one guard.");
        Entry("Guarded.replace_inverse", "Both inverse laws",
            Base(And(Equal(Rep(Inv(I("pi")), Rep(I("pi"), I("x"))), I("x")),
                Equal(Rep(I("pi"), Rep(Inv(I("pi")), I("x"))), I("x"))),
                B("pi", Perm), B("x", SeqType)),
            "Both inverse equations consume eligibility invariance and composition; "
            + "no inverse automorphism is supplied as an assumption.");
        Entry("Guarded.replace_local", "A uniform finite original-edge window",
            Base(Imp(All(Imp(And(Le(Sub(I("t"), Radius), I("s")),
                    Le(I("s"), Add(I("t"), Radius))), Equal(At(I("x"), I("s")),
                    At(I("y"), I("s")))), B("s", I("Int"))),
                Equal(At(Rep(I("pi"), I("x")), I("t")),
                    At(Rep(I("pi"), I("y")), I("t")))),
                B("pi", Perm), B("x", SeqType), B("y", SeqType), B("t", I("Int"))),
            "Radius m+d suffices. Every template relevant at t lies in the displayed "
            + "closed interval. Transporting its finite tests proves local dependence, "
            + "which factors replacement through a finite discrete window for continuity.");
        Entry("Guarded.replace_translate", "Commutation with integer translation",
            Base(Equal(At(Rep(I("pi"), Call("translateSequence", I("c"), I("x"))), I("t")),
                At(Rep(I("pi"), I("x")), Add(I("t"), I("c")))),
                B("pi", Perm), B("x", SeqType), B("c", I("Int")), B("t", I("Int"))),
            "translateSequence(c,x)(s)=x(s+c). Translation carries selected starts "
            + "by the same integer displacement; c=1 is the actual unit left shift.");
        Entry("Guarded.Loops", "Legal common-endpoint finite loops",
            Base(All(Typed(Call("Loops", I("W"), I("G"), I("p")), I("Prop")),
                B("V", I("Type")), B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                B("p", I("V")))),
            "Loops requires 0<d, all interior target/source seams of marker and data, "
            + "and source(first)=target(last)=p for marker and every data word. It stores "
            + "only these finite graph facts. The Reset specialization proves every field.", true);
        Entry("Guarded.onHistory", "Replacement of actual legal histories",
            LoopScope(Typed(Call("onHistory", I("W"), I("G"), I("L"), I("pi"), I("x")),
                Call("History", I("G"))), false, false,
                B("pi", Perm), B("x", Call("History", I("G")))),
            "History G is the original legal subtype of Int→E. Internal replacements use "
            + "data legality; the final data edge meets the untouched right guard at p; "
            + "the first data edge meets the old left seam at p. All other seams are unchanged.", true);
        Entry("Guarded.homeomorph", "The genuine history homeomorphism",
            LoopScope(Typed(Call("homeomorph", I("W"), I("G"), I("L"), I("pi")),
                Call("Homeomorph", Call("History", I("G")), Call("History", I("G")))),
                true, false, B("pi", Perm)),
            "The edge topology is discrete. Both directions are onHistory with pi and "
            + "pi inverse; finite-window dependence proves continuity in the original "
            + "product/subtype topology, and replace_inverse proves both inverse laws.", true);
        Entry("Guarded.action", "A hom into the full UNIT-shift centralizer",
            LoopScope(Typed(Action, Call("MonoidHom", Perm, Call("FullAut", I("G")))),
                true, true),
            "FullAut is StandardBeamHomeomorphisms.fullAutSubgroup: every actual history "
            + "homeomorphism commuting with UNIT shift. The displayed finite/discrete "
            + "instances are the exact domain requirements. The hom uses ordinary composition.", true);
        Entry("Guarded.action_injective", "Faithfulness on actual histories",
            LoopScope(Call("FunctionInjective", Action), true, true,
                B("hG", Call("Essential", I("G")))),
            "For each i, the positive legal word M D_i M extends to an actual history "
            + "by exists_history_containing. Its central gap remains selected independently "
            + "of the exterior extension. Equality of actions forces equality of encoded data, "
            + "then equality of permutation values by the injective data family.");
        Entry("resetMarker", "The exact numbered Reset marker",
            ResetScope(Typed(Call("resetMarker", I("hq")), Fn(Call("Fin", M), Edges)), false),
            "Marker edges are transported by originalEdge from B^(2k+1)A. A=ab and B=acd: "
            + "a is reset 0→0 at absolute sign 1, b is reset 0→0 at sign zeta, c is advance "
            + "0→1 at sign zeta, d is reset 1→0 at sign zeta. Reset edges have flip label, "
            + "advance has identity label, and all edge numbers are the proved unique zero. "
            + "zeta=Multiplicative.ofAdd true, p=(0,1).", true);
        Entry("resetData", "The Boolean indexed six-edge data words",
            ResetScope(Typed(Call("resetData", I("hq"), I("b")), Fn(Call("Fin", Dlen), Edges)),
                false, B("b", Bits)),
            "Each Boolean true chooses A^3, each false chooses B^2. All k chunks have "
            + "length six and endpoints p. Their second edges differ, giving injectivity "
            + "by equal-length chunk splitting, without a free-shift conjugacy.", true);
        Entry("resetWords", "Discharged original finite-word hypotheses",
            ResetScope(Typed(Call("resetWords", I("hq")),
                Call("GuardedWords", Edges, Bits, M, Dlen)), false),
            "The expanded edge b appears only at the marker's final position. Every "
            + "proper prefix excludes it while every suffix ends in it, proving edge "
            + "unborderedness at all offsets. Data length 6k is less than marker length "
            + "6k+5, independently of the data contents.", true);
        Entry("resetLoops", "Discharged legality and endpoint hypotheses",
            ResetScope(Call("Loops", Call("resetWords", I("hq")), Graph,
                Call("origin", I("q"))), true),
            "Existing actual_source and actual_target transport the original ListPath "
            + "proofs for A, B, repeats and concatenated chunks. Every loop returns to "
            + "the same original vertex p; q need not be even. origin(q) denotes (0,1).", true);
        Entry("resetAction", "The original Reset history permutation action",
            ResetScope(Typed(Call("resetAction", I("hq"), I("hk")),
                Call("MonoidHom", Call("Perm", Bits), Call("FullAut", Graph))), true),
            "This instantiates the checked guarded action on actual expanded Reset edges. "
            + "Extra q>2 edges and arbitrary noncoded tails remain in its domain. Its "
            + "symmetric original-edge window has radius m+d=12k+5.", true);
        Entry("resetAction_injective", "The original Reset action is faithful",
            ResetScope(Call("FunctionInjective", Call("resetAction", I("hq"), I("hk"))), true),
            "reset_expanded_essential supplies essentiality for every positive q, and the "
            + "general action_injective theorem uses the exact original finite-word realization. "
            + "This is consumed by the original representation-kernel embedding.");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Uniform guarded marker permutations on original numbered Reset histories.",
            H("Original finite-window dynamics"),
            Blocks([Paragraph(Text(
                "The simultaneous M D_i M method is classical: Boyle–Lind–Rudolph, "
                + "The automorphism group of a shift of finite type, Trans. AMS 306 (1988), "
                + "71–114, section 2 pp. 74–75, DOI 10.1090/S0002-9947-1988-0927684-2. "
                + "The new formal content is the arbitrary-history guard protection and "
                + "eligible-interval invariance, with every finite-word hypothesis verified "
                + "on the original ResetGraph. No publication novelty is claimed.")),
                Paragraph(Text(
                "The original history action connects to arithmetic through ResetHistoryKernel: "
                + "the cyclic native chart makes the actual rho image abelian, so the alternating "
                + "restrictions give nonabelian finite subgroups of unbounded orders in its kernel. "
                + "This describes a subgroup family, not the complete kernel or a claim that the "
                + "whole kernel is locally finite. Display aliases denote the exact typed functions "
                + "described in each entry; graph edge labels, multiplicities and absolute signs remain.")),
                .. entries])));
    }
}
