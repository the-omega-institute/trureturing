using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EscapeSpectrum;

internal sealed class UncountableSingletonCutCountermodelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/EscapeSpectrum/UncountableSingletonCutCountermodel.";
    private static Formula J => Call("unitInterval");
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula NonnegativeReal => Call("NNReal");
    private static Formula BoolType => Call("Bool");
    private static Formula X => F.Id("X");
    private static Formula Pair => Seq(X, Sp, Times, Sp, X);
    private static Formula Q => F.Id("q");
    private static Formula Target => F.Id("T");
    private static Formula Definitions => F.Id("d");
    private static Formula Cost => F.Id("c");
    private static Formula Edge => F.Id("e");
    private static Formula Algebra => F.Id("A");
    private static Formula Charge => Nu;
    private static Formula Weight => F.Id("w");
    private static Formula E => F.Id("E");
    private static Formula U => F.Id("U");
    private static Formula Blind => F.Id("B");
    private static Formula Residual => F.Id("R");
    private static Formula Removed => F.Id("P");
    private static Formula GammaType => Call("Subtype", Gamma);
    private static Formula Selections => Call("Finset", GammaType);
    private static Formula Family => Seq(F.Id("i"), Colon, Sp, GammaType, Sp, Mapsto, Sp,
        App(Definitions, Call("val", F.Id("i"))));
    private static Formula CarrierVal => Call("SubtypeVal", Call("Subtype", E));
    private static Formula IntervalVal => Call("SubtypeVal", J);
    private static Formula FullCover => Call("iUnion",
        Seq(F.Id("i"), Colon, Sp, GammaType), App(U, F.Id("i")));
    private static Formula SetOf(Formula type) => Call("Set", type);
    private static Formula App(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula body) => Seq(Open, body, Close, Sp, Land);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Subset(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula Difference(Formula a, Formula b) => Seq(a, Sp, Setminus, Sp, b);
    private static Formula Implies(Formula a, Formula b) => Seq(Open, a, Close, Sp, Rightarrow, Sp, b);
    private static Formula Both(Formula a, Formula b) => Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula Positive(Formula a) => Seq(D(0), Sp, Lt, Sp, a);
    private static Formula Nonnegative(Formula a) => Seq(D(0), Sp, Leq, Sp, a);
    private static Formula Section(Formula b, Formula c) => Call("preimage", App(Edge, b), c);
    private static Formula RealImage(Formula a) => Call("image", IntervalVal, a);
    private static Formula Measurable(Formula a, Formula measure) => Call("NullMeasurableSet", a, measure);
    private static Formula RealVolume => Call("volume", Real);
    private static Formula WeightMass(Formula c) => Call("mass", Weight, c);
    private static Formula ChargeMass(Formula c) => App(Charge, c);
    private static Formula CutUnion(Formula s) => Call("iUnion",
        Seq(F.Id("i"), Sp, InMacro, Sp, s), App(U, F.Id("i")));
    private static Formula HalfSum(Formula c) => Seq(
        Frac, Grp(D(1)), Grp(D(2)), Sp,
        Call("toNNReal", App(Mu, Section(Call("false"), c))), Sp, Plus, Sp,
        Frac, Grp(D(1)), Grp(D(2)), Sp,
        Call("toNNReal", App(Mu, Section(Call("true"), c))));
    private static Formula SelectionCost(Formula s) => Call("finiteSelectionCost", Gamma, Cost, s);
    private static Formula Mass(Formula s) =>
        Call("finiteResidualMass", Gamma, Definitions, Q, Target, Weight, s);
    private static Formula Values(Formula l) =>
        Call("finiteBudgetMassValues", Gamma, Definitions, Q, Target, Cost, Weight, l);
    private static Formula Spectrum(Formula l) =>
        Call("finiteEscapeSpectrum", Gamma, Definitions, Q, Target, Cost, Weight, l);
    private static Formula SpectrumFunction =>
        Call("finiteEscapeSpectrum", Gamma, Definitions, Q, Target, Cost, Weight);
    private static Formula BlindRatio => Seq(Frac, Grp(WeightMass(Blind)), Grp(WeightMass(E)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uncountably many singleton cuts cover every defect edge, while each finite "
            + "selection leaves Lebesgue charge one and escape spectrum one.",
        H("Uncountable Singleton Cut Countermodel"),
        Blocks(
            Paragraph(Text("Let J be the actual closed unit interval in the real numbers, "
                + "with its Lebesgue probability measure mu, and let X be J times Bool. "
                + "The base readout reads the interval coordinate and the target reads the "
                + "Boolean coordinate. Every t in J supplies the definition d_t(s,i), equal "
                + "to i when s=t and false otherwise. All definitions have cost one.")),
            Paragraph(Math(ObjectsFormula())),
            Paragraph(Text("The supported algebra contains exactly the subsets of E whose "
                + "two interval sections are NullMeasurableSet for mu. This predicate is "
                + "measurability for completed Lebesgue measure. Under the interval inclusion, "
                + "it is equivalent to Lebesgue measurability of the real image, with the "
                + "same measure on every interval set. The half-sum formula defines nu on "
                + "every ambient set of pairs. Interval probability makes both section "
                + "measures finite, so their toNNReal conversions preserve their values. "
                + "The real weight w is the coercion of this same AddContent.")),
            Claim("finite-null-deletion", "finite_residual_mass_eq_one",
                "Every finite residual has mass one",
                Disp(All(F.Id("S"), Selections, Equal(Mass(F.Id("S")), D(1)))),
                "For every finite selection S from the full language, the actual "
                    + "Option-valued finiteSelectionSupplement leaves each directed edge "
                    + "precisely when its basepoint is absent from P(S). The finite image "
                    + "P(S) has Lebesgue measure zero. Both residual sections therefore "
                    + "have measure one, and their half-sum is one."),
            Claim("complete-continuum-countermodel", "uncountable_singleton_cut_countermodel",
                "The full uncountable cover and all finite budget spectra", FullFormula(),
                "The interval language is nonempty and uncountable. Evaluation at (t,true) "
                    + "distinguishes its definitions, so their range is uncountable as well. "
                    + "Each singleton cut contains exactly the two directed edges over its "
                    + "basepoint. Every edge is cut by its own definition; this proves the "
                    + "full cover pointwise and makes the common blind residual empty. "
                    + "The algebra is a ring with complements relative to E, and the subtype "
                    + "carrier correspondence is exact in both directions. The charge is "
                    + "supported on E, has total mass one, is globally monotone and "
                    + "nonnegative, and is additive for disjoint algebra members. Finite "
                    + "cut unions have mass zero; each residual and its difference from B "
                    + "belong to the algebra and satisfy the common blind decomposition. "
                    + "A finite selection costs its cardinality. The empty selection is "
                    + "affordable for every NNReal budget, including zero. The finite "
                    + "residual equality gives the affordable mass set {1}, hence canonical "
                    + "spectrum one at every budget. The positive baseline and global "
                    + "monotonicity identify its limit with the all-finite infimum one. "
                    + "The blind ratio is zero and differs strictly from that limit. "
                    + "The full uncountable cover is a pointwise identity; each budget "
                    + "continues to permit only finite selections."))));

    private static DocumentBlock Claim(string id, string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula ObjectsFormula()
    {
        Formula s = F.Id("S"), t = F.Id("t"), b = F.Id("b"), c = F.Id("C");
        Formula x = F.Id("s"), i = F.Id("i");
        Formula point = Seq(Open, x, Comma, i, Close);
        return Disp(new Formula.Aligned([
            Equal(J, Call("Icc", D(0), D(1))),
            Equal(X, Seq(J, Sp, Times, Sp, BoolType)),
            Equal(Gamma, Call("univ", J)), Equal(Mu, Call("volume", J)),
            Equal(Q, Call("fst")), Equal(Target, Call("snd")),
            All(t, J, All(x, J, All(i, BoolType, Equal(App(App(Definitions, t), point),
                Call("ite", Equal(x, t), i, Call("false")))))),
            All(t, J, Equal(App(Cost, t), D(1))),
            All(b, BoolType, All(t, J, Equal(App(App(Edge, b), t), Seq(Open,
                Open, t, Comma, b, Close, Comma,
                Open, t, Comma, Call("BoolNot", b), Close, Close)))),
            Equal(E, Call("defectRelation", Q, Target)),
            All(i, GammaType, Equal(App(U, i), Call("inter", E,
                Call("compl", Call("conceptKernel", Family, i))))),
            Equal(Blind, Call("inter", E, Call("jointKernel", Family))),
            All(s, Selections, Equal(App(Residual, s), Call("defectRelation",
                Call("conceptJoin", Q, Call("finiteSelectionSupplement", Gamma, Definitions, s)), Target))),
            All(s, Selections, Equal(App(Removed, s), Call("image", Call("val"), Call("coeSet", s)))),
            Equal(Algebra, Call("setOf", Seq(c, Colon, Sp, SetOf(Pair)),
                Both(Subset(c, E), All(b, BoolType, Measurable(Section(b, c), Mu))))),
            Seq(Charge, Colon, Sp, Call("AddContent", NonnegativeReal, Algebra)),
            All(c, SetOf(Pair), Equal(ChargeMass(c), HalfSum(c))),
            Seq(Weight, Colon, Sp, Call("EscapeWeight", Pair)),
            All(c, SetOf(Pair), Equal(WeightMass(c), Call("coeReal", ChargeMass(c)))),
        ]));
    }

    private static Formula FullFormula()
    {
        Formula a = F.Id("a"), c = F.Id("C"), d = F.Id("D");
        Formula b = F.Id("b"), i = F.Id("i"), t = F.Id("t");
        Formula s = F.Id("S"), l = F.Id("L"), rs = App(Residual, s), ps = App(Removed, s);
        Formula allInf = Call("allFiniteResidualInfimum", Gamma, Definitions, Q, Target, Weight);
        Formula relative = Difference(rs, Blind);
        return Disp(new Formula.Aligned([
            And(Seq(Neg, Sp, Call("Countable", Gamma))),
            And(Call("Nonempty", Gamma)), And(Call("Injective", Family)),
            And(Seq(Neg, Sp, Call("Countable", Call("range", Family)))),
            And(Equal(E, Seq(Call("range", App(Edge, Call("false"))), Sp, Cup, Sp,
                Call("range", App(Edge, Call("true")))))),
            And(All(a, SetOf(J), Both(
                Seq(Measurable(a, Mu), Sp, Leftrightarrow, Sp, Measurable(RealImage(a), RealVolume)),
                Equal(App(Mu, a), App(RealVolume, RealImage(a)))))),
            And(All(c, SetOf(Pair), Seq(Member(c, Algebra), Sp, Leftrightarrow, Sp,
                Both(Subset(c, E), All(b, BoolType, Measurable(RealImage(Section(b, c)), RealVolume)))))),
            And(All(d, SetOf(Call("Subtype", E)), Equal(
                Call("preimage", CarrierVal, Call("image", CarrierVal, d)), d))),
            And(All(c, SetOf(Pair), Implies(Subset(c, E), Equal(
                Call("image", CarrierVal, Call("preimage", CarrierVal, c)), c)))),
            And(Call("IsSetRing", Algebra)), And(Member(Emptyset, Algebra)), And(Member(E, Algebra)),
            And(All(c, SetOf(Pair), Implies(Member(c, Algebra), Member(Difference(E, c), Algebra)))),
            And(All(c, SetOf(Pair), Equal(ChargeMass(c), HalfSum(c)))),
            And(All(c, SetOf(Pair), Equal(WeightMass(c), Call("coeReal", ChargeMass(c))))),
            And(Equal(ChargeMass(Emptyset), D(0))), And(Equal(ChargeMass(E), D(1))),
            And(All(c, SetOf(Pair), Nonnegative(WeightMass(c)))),
            And(Call("Monotone", Charge)), And(Call("Monotone", Call("mass", Weight))),
            And(All(c, SetOf(Pair), All(d, SetOf(Pair), Implies(
                Both(Member(c, Algebra), Both(Member(d, Algebra), Call("Disjoint", c, d))),
                Equal(ChargeMass(Seq(c, Sp, Cup, Sp, d)),
                    Seq(ChargeMass(c), Sp, Plus, Sp, ChargeMass(d))))))),
            And(All(c, SetOf(Pair), Equal(ChargeMass(c), ChargeMass(Call("inter", c, E))))),
            And(Positive(WeightMass(E))),
            And(Seq(Call("coeENNReal", ChargeMass(E)), Sp, Lt, Sp, Infty)),
            And(All(i, GammaType, Both(Equal(App(U, i), Seq(OpenBrace,
                App(App(Edge, Call("false")), Call("val", i)), Comma,
                App(App(Edge, Call("true")), Call("val", i)), CloseBrace)), Member(App(U, i), Algebra)))),
            And(Equal(FullCover, E)), And(Equal(Blind, Difference(E, FullCover))),
            And(Equal(Blind, Emptyset)), And(Member(Blind, Algebra)),
            And(All(s, Selections, Call("Finite", ps))),
            And(All(s, Selections, Equal(App(Mu, ps), D(0)))),
            And(All(s, Selections, Equal(rs, Difference(E, CutUnion(s))))),
            And(All(s, Selections, All(b, BoolType, Equal(Section(b, rs), Call("compl", ps))))),
            And(All(s, Selections, Member(CutUnion(s), Algebra))),
            And(All(s, Selections, Member(rs, Algebra))),
            And(All(s, Selections, Member(relative, Algebra))),
            And(All(s, Selections, Equal(ChargeMass(CutUnion(s)), D(0)))),
            And(All(s, Selections, Subset(Blind, rs))),
            And(All(s, Selections, Equal(ChargeMass(rs), D(1)))),
            And(All(s, Selections, Equal(ChargeMass(rs),
                Seq(ChargeMass(Blind), Sp, Plus, Sp, ChargeMass(relative))))),
            And(All(s, Selections, Equal(Mass(s), D(1)))),
            And(All(t, J, Implies(Member(t, Gamma), Positive(App(Cost, t))))),
            And(All(s, Selections, Equal(SelectionCost(s), Call("coeReal", Call("card", s))))),
            And(All(l, NonnegativeReal, Seq(SelectionCost(Emptyset), Sp, Leq, Sp, Call("coeReal", l)))),
            And(All(l, NonnegativeReal, Equal(Values(l), Seq(OpenBrace, D(1), CloseBrace)))),
            And(All(l, NonnegativeReal, Equal(Spectrum(l), D(1)))),
            And(Equal(allInf, D(1))),
            And(Call("Tendsto", SpectrumFunction, Call("atTop"), Call("nhds", D(1)))),
            And(Equal(BlindRatio, D(0))), NotEqual(D(1), BlindRatio),
        ]));
    }
}
