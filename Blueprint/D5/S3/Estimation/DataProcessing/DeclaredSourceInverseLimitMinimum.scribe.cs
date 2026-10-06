using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class DeclaredSourceInverseLimitMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact label and joint-source constraints on arbitrary finite towers have an attained "
            + "completed total-variation minimum equal to the supremum of finite minima.",
        H("Nearest Laws With Declared Joint Sources"),
        Blocks(Describe.Lean(
            DescribeId.Create("declared-source-inverse-limit-minimum"),
            DeclarationHandle.Create(
                "D5/S3/Estimation/DataProcessing/DeclaredSourceInverseLimitMinimum.exists_minimum_eq_iSup"),
            H("One completed feasible law realizes the finite-minimum supremum"),
            StatementSource.FromAuthor(FullStatement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "W_l, Z_l and U_l are finite nonempty discrete Borel spaces at every natural "
                        + "level. Their total bonding maps alpha_l, beta_l and gamma_l need not be "
                        + "surjective. The finite label map W_l to Z_l and joint-source map W_l to U_l "
                        + "commute with the respective bonds.")),
                Paragraph(Text(
                    "The completed carriers are the actual inverse-limit thread subtypes. The "
                        + "measurable maps f and g from the completed world carrier have coordinates "
                        + "label_l(x_l) and source_l(x_l). One actual Borel probability rho on the "
                        + "world threads determines every actual finite world law and every finite "
                        + "or completed source law by pushforward.")),
                Paragraph(Text(
                    "In the formula, map is probability pushforward, mass is the underlying "
                        + "measure on an event, real is its real-valued mass, and toMeasure is the "
                        + "underlying-measure coercion. completion uses the measure completion and "
                        + "toReal converts its finite event mass to a real number; ofReal is "
                        + "ENNReal.ofReal. Thread has the subtype topology of the product and its "
                        + "Borel measurable structure. ProbabilityMeasure carries the weak topology; "
                        + "L and H carry their respective subtype and product-subtype topologies. "
                        + "The existentially quantified F, L, H and cost functions are fixed by the "
                        + "displayed defining equations, equivalently the local let definitions "
                        + "in the Lean statement.")),
                Paragraph(Text(
                    "For every choice of the stated carriers, maps, laws and sets satisfying "
                        + "these hypotheses, there exists Qinf for which all the conclusions below "
                        + "hold together. The target laws Q_l on Z_l are given with exact beta compatibility. The "
                        + "completed target Qinf is constructed on the actual label threads and has "
                        + "exactly those projections. The construction uses probability extension "
                        + "without surjectivity of the original bonds."),
                    Ref("D5/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension.exists_unique_extension")),
                Paragraph(Text(
                    "Legal sets A_l in W_l satisfy alpha_l(A_(l+1)) contained in A_l. The completed "
                        + "legal set is exactly the intersection of their coordinate cylinders. "
                        + "F_l consists of all probabilities theta_l with label pushforward Q_l, "
                        + "source pushforward equal to the actual joint-source law, and mass one on A_l. "
                        + "Each F_l is assumed nonempty with all three constraints satisfied together.")),
                Paragraph(Text(
                    "L consists of all completed probabilities theta with f-pushforward Qinf, "
                        + "g-pushforward equal to the g-pushforward of rho, and mass one on the completed "
                        + "legal set. No actual-legality assumption is imposed on rho. Arbitrary real "
                        + "probability masses, including zeros, remain allowed. The carriers are not "
                        + "required to be cyclic tuples and there are no permutation, cut or excess premises.")),
                Paragraph(Text(
                    "For every finite candidate probability, eventCost_l is the supremum of absolute "
                        + "differences of event probabilities from the actual finite world law. It is "
                        + "exactly one half of the sum of the absolute singleton-mass differences. "
                        + "completedEventCost is the same event supremum for rho and theta on the "
                        + "full Borel thread event domain.")),
                Paragraph(Text(
                    "commonCost uses the completed measures on events null-measurable for rho+theta. "
                        + "The theorem returns equality of completedEventCost and commonCost. Both "
                        + "costs are lower semicontinuous for the weak probability topology, on the "
                        + "whole completed probability space and on its feasible subtype L. "
                        + "This gives four lower-semicontinuity assertions, with no weak-continuity claim.")),
                Paragraph(Text(
                    "L is compact. Let H be the space of all compatible families with the l-th law "
                        + "in F_l, carrying the subtype topology of the product of weak probability spaces. "
                        + "There is a homeomorphism E from L to H whose l-th coordinate is the actual "
                        + "pushforward of theta along the l-th world projection.")),
                Paragraph(Text(
                    "For every pair of feasible completed laws and every real t between zero and one, "
                        + "their probability mixture remains feasible and E sends it to the same "
                        + "coordinatewise mixture. Conversely, a coordinatewise mixture of compatible "
                        + "families is sent by the inverse homeomorphism to the corresponding mixture "
                        + "of completed laws. These are the two explicit affine directions.")),
                Paragraph(Text(
                    "There are real numbers d_l, each attained as the minimum of eventCost_l over "
                        + "the exact F_l. They lie in [0,1], are monotone and converge to their supremum. "
                        + "One theta in L has completedEventCost equal to that supremum. Every completed "
                        + "feasible competitor has cost at least the supremum, so the same theta "
                        + "attains the completed minimum.")),
                Paragraph(Text(
                    "For every real c at least zero, one completed feasible law has cost at most c "
                        + "if and only if each finite level has a feasible law of cost at most c. "
                        + "The construction uses the same c at all levels, selecting a compatible "
                        + "family inside the compact radius-constrained classes. It does not assume "
                        + "that independently chosen finite minimizers are compatible.")),
                Paragraph(Text(
                    "The finite feasible classes are closed probability constraints. Their bonding "
                        + "maps preserve the label target, the actual joint-source target and legal "
                        + "support. Pushforward contraction and the full-event total-variation "
                        + "identity give the common-radius upper bound and the lower bound from "
                        + "every completed competitor. Compact selection is applied to probability "
                        + "spaces, whose carriers need not be finite or whose bonds need not be surjective.")),
                Paragraph(Text(
                    "Uniqueness of extension for a fixed compatible law family gives no uniqueness "
                        + "of an optimizer or original world. No measurable selection, arbitrary "
                        + "event-domain enlargement, or extension of every preassigned finite candidate "
                        + "is asserted. U_l records the source variables declared in this model; "
                        + "additional archive or mechanism restrictions need their own exact semantics."))),
            DescribeRole.Theorem))));
    private static Formula FullStatement()
    {
        var n = FormulaDsl.Seq(FormulaDsl.Mathbb, FormulaDsl.Grp(Id("N")));
        var r = FormulaDsl.Seq(FormulaDsl.Mathbb, FormulaDsl.Grp(Id("R")));
        var typeFamily = new Formula.TypeArrow(n, Id("Type"));
        var l = Id("l");
        var next = new Formula.Binary(l, FormulaBinaryOperator.Add, Num(1));
        var w = Call("W", l);
        var z = Call("Z", l);
        var u = Call("U", l);
        var tw = Call("Thread", Id("W"), Id("alpha"));
        var tz = Call("Thread", Id("Z"), Id("beta"));
        var tu = Call("Thread", Id("U"), Id("gamma"));
        var probW = Call("ProbabilityMeasure", w);
        var probThread = Call("ProbabilityMeasure", tw);
        var family = DependentProduct("l", n, probW);
        var rho = Id("rho");
        var theta = Id("theta");
        var eta = Id("eta");
        var f = Id("f");
        var g = Id("g");
        var rhoLevel = Map(rho, Call("pi", l));
        var finiteConstraints = And(
            Equal(Map(theta, Call("label", l)), Call("Q", l)),
            Equal(Map(theta, Call("source", l)), Map(rhoLevel, Call("source", l))),
            Equal(Call("mass", theta, Call("A", l)), Num(1)));
        var finiteFeasible = Call("F", l);
        var finiteCost = Call("eventCost", l, theta);
        var completedCost = Call("completedEventCost", theta);
        var dsup = Call("sSup", Call("range", Id("d")));
        var legal = Comprehension("x", tw, All("l", n,
            Member(Call("pi", l, Id("x")), Call("A", l))));
        var definitions = ConjunctionRows(
            All("l", n, All("theta", probW,
                Iff(Member(theta, finiteFeasible), finiteConstraints))),
            All("theta", probThread, Iff(Member(theta, Id("L")), And(
                Equal(Map(theta, f), Id("Qinf")),
                Equal(Map(theta, g), Map(rho, g)),
                Equal(Call("mass", theta, legal), Num(1))))),
            All("eta", family, Iff(Member(eta, Id("H")), And(
                All("l", n, Member(Call("eta", l), finiteFeasible)),
                All("l", n, Equal(Map(Call("eta", next), Call("alpha", l)), Call("eta", l)))))),
            All("l", n, All("theta", probW, Equal(finiteCost,
                Call("sSup", new Formula.SetBuilder(
                    Gap(rhoLevel, theta, Id("E")), Id("E"),
                    Comprehension("E", Call("Set", w), Call("MeasurableSet", Id("E")))))))),
            All("theta", probThread, Equal(completedCost,
                Call("sSup", new Formula.SetBuilder(
                    Gap(rho, theta, Id("E")), Id("E"),
                    Comprehension("E", Call("Set", tw), Call("MeasurableSet", Id("E"))))))),
            All("theta", probThread, Equal(Call("commonCost", theta),
                Call("sSup", new Formula.SetBuilder(
                    new Formula.Absolute(new Formula.Binary(
                        Call("toReal", Call("completion", rho, Id("E"))),
                        FormulaBinaryOperator.Subtract,
                        Call("toReal", Call("completion", theta, Id("E"))))),
                    Id("E"), Comprehension("E", Call("Set", tw),
                        Call("NullMeasurableSet", Id("E"),
                            new Formula.Binary(rho, FormulaBinaryOperator.Add, theta))))))));
        var normalization = All("l", n, All("theta", probW, Equal(finiteCost,
            new Formula.Binary(new Formula.Fraction(Num(1), Num(2)),
                FormulaBinaryOperator.Multiply,
                FormulaDsl.Seq(FormulaDsl.Sum,
                    FormulaDsl.Underscore, FormulaDsl.Grp(Member(Id("w"), w)),
                    Gap(rhoLevel, theta, new Formula.SetLiteral([Id("w")])))))));
        var forwardAffine = AllMany([
            Variable("theta", Id("L")), Variable("eta", Id("L")), Variable("t", r)],
            Implies(And(Le(Num(0), Id("t")), Le(Id("t"), Num(1))),
                Some("zeta", Id("L"), And(
                    Equal(Call("toMeasure", Id("zeta")), Mixture(theta, eta)),
                    All("l", n, Equal(Call("toMeasure", Call("coordinate", Call("e", Id("zeta")), l)),
                        Mixture(Call("coordinate", Call("e", theta), l),
                            Call("coordinate", Call("e", eta), l))))))));
        var inverseAffine = AllMany([
            Variable("a", Id("H")), Variable("b", Id("H")), Variable("h", Id("H")),
            Variable("t", r)], Implies(
                And(Le(Num(0), Id("t")), Le(Id("t"), Num(1)),
                    All("l", n, Equal(Call("toMeasure", Call("h", l)), Mixture(Call("a", l), Call("b", l))))),
                Equal(Call("toMeasure", Call("inverse", Id("e"), Id("h"))),
                    Mixture(Call("inverse", Id("e"), Id("a")),
                        Call("inverse", Id("e"), Id("b"))))));
        var homeomorphism = Some("e", Call("Homeomorph", Id("L"), Id("H")), And(
            All("theta", Id("L"), All("l", n,
                Equal(Call("coordinate", Call("e", theta), l), Map(theta, Call("pi", l))))),
            forwardAffine, inverseAffine));
        var minimum = Some("d", new Formula.TypeArrow(n, r), ConjunctionRows(
            All("l", n, Some("theta", finiteFeasible, And(
                Equal(finiteCost, Call("d", l)),
                All("eta", finiteFeasible, Le(Call("d", l), Call("eventCost", l, eta)))))),
            AllMany([Variable("i", n), Variable("j", n)],
                Implies(Le(Id("i"), Id("j")), Le(Call("d", Id("i")), Call("d", Id("j"))))),
            All("l", n, And(Le(Num(0), Call("d", l)), Le(Call("d", l), Num(1)))),
            Call("Tendsto", Id("d"), Id("atTop"), Call("nhds", dsup)),
            All("c", r, Implies(Le(Num(0), Id("c")), Iff(
                Some("theta", Id("L"), Le(completedCost, Id("c"))),
                All("l", n, Some("theta", finiteFeasible, Le(finiteCost, Id("c"))))))),
            Some("thetaStar", Id("L"), And(
                Equal(Call("completedEventCost", Id("thetaStar")), dsup),
                All("eta", Id("L"), Le(dsup, Call("completedEventCost", eta))),
                All("eta", Id("L"), Le(Call("completedEventCost", Id("thetaStar")),
                    Call("completedEventCost", eta)))))));
        var output = Some("Qinf", Call("ProbabilityMeasure", tz), And(
            All("l", n, Equal(Map(Id("Qinf"), Call("pi", l)), Call("Q", l))),
            SomeMany([
                Variable("F", DependentProduct("l", n, Call("Set", probW))),
                Variable("L", Call("Set", probThread)), Variable("H", Call("Set", family)),
                Variable("eventCost", DependentProduct("l", n, new Formula.TypeArrow(probW, r))),
                Variable("completedEventCost", new Formula.TypeArrow(probThread, r)),
                Variable("commonCost", new Formula.TypeArrow(probThread, r))],
                ConjunctionRows(definitions, Call("IsCompact", Id("L")), normalization,
                    All("theta", probThread, Equal(completedCost, Call("commonCost", theta))),
                    Call("LowerSemicontinuous", Id("completedEventCost")),
                    Call("LowerSemicontinuous", Id("commonCost")),
                    Call("LowerSemicontinuous", Lambda("theta", Id("L"), completedCost)),
                    Call("LowerSemicontinuous", Lambda("theta", Id("L"), Call("commonCost", theta))),
                    homeomorphism, minimum))));
        var hypotheses = ConjunctionRows(
            All("l", n, And(
                Call("Finite", w), Call("Nonempty", w),
                Call("DiscreteTopology", w, Call("TW", l)), Call("BorelSpace", w, Call("TW", l), Call("MW", l)),
                Call("Finite", z), Call("Nonempty", z),
                Call("DiscreteTopology", z, Call("TZ", l)), Call("BorelSpace", z, Call("TZ", l), Call("MZ", l)),
                Call("Finite", u), Call("Nonempty", u),
                Call("DiscreteTopology", u, Call("TU", l)), Call("BorelSpace", u, Call("TU", l), Call("MU", l)))),
            All("l", n, All("x", Call("W", next), And(
                Equal(Call("label", l, Call("alpha", l, Id("x"))),
                    Call("beta", l, Call("label", next, Id("x")))),
                Equal(Call("source", l, Call("alpha", l, Id("x"))),
                    Call("gamma", l, Call("source", next, Id("x"))))))),
            Call("Measurable", f), Call("Measurable", g),
            All("x", tw, All("l", n, And(
                Equal(Call("pi", l, Call("f", Id("x"))), Call("label", l, Call("pi", l, Id("x")))),
                Equal(Call("pi", l, Call("g", Id("x"))), Call("source", l, Call("pi", l, Id("x"))))))),
            All("l", n, Equal(Map(Call("Q", next), Call("beta", l)), Call("Q", l))),
            All("l", n, All("x", Call("A", next), Member(Call("alpha", l, Id("x")), Call("A", l)))),
            All("l", n, Some("theta", probW, finiteConstraints)));
        var telescope = AllMany([
            Variable("W", typeFamily), Variable("Z", typeFamily), Variable("U", typeFamily)],
            AllMany([
                Variable("TW", DependentProduct("l", n, Call("TopologicalSpace", w))),
                Variable("TZ", DependentProduct("l", n, Call("TopologicalSpace", z))),
                Variable("TU", DependentProduct("l", n, Call("TopologicalSpace", u))),
                Variable("MW", DependentProduct("l", n, Call("MeasurableSpace", w))),
                Variable("MZ", DependentProduct("l", n, Call("MeasurableSpace", z))),
                Variable("MU", DependentProduct("l", n, Call("MeasurableSpace", u))),
                Variable("alpha", DependentProduct("l", n, new Formula.TypeArrow(Call("W", next), w))),
                Variable("beta", DependentProduct("l", n, new Formula.TypeArrow(Call("Z", next), z))),
                Variable("gamma", DependentProduct("l", n, new Formula.TypeArrow(Call("U", next), u))),
                Variable("label", DependentProduct("l", n, new Formula.TypeArrow(w, z))),
                Variable("source", DependentProduct("l", n, new Formula.TypeArrow(w, u))),
                Variable("f", new Formula.TypeArrow(tw, tz)), Variable("g", new Formula.TypeArrow(tw, tu)),
                Variable("Q", DependentProduct("l", n, Call("ProbabilityMeasure", z))),
                Variable("A", DependentProduct("l", n, Call("Set", w))), Variable("rho", probThread)],
                Implies(hypotheses, output)));
        var b = Call("B", l);
        var bonds = DependentProduct("l", n,
            new Formula.TypeArrow(Call("B", next), b));
        var threads = Call("Thread", Id("B"), Id("q"));
        return new Formula.Aligned([
            AllMany([Variable("B", typeFamily), Variable("q", bonds)],
                Equal(threads, Comprehension("x", DependentProduct("l", n, b),
                    All("l", n, Equal(Call("q", l, Call("coordinate", Id("x"), next)),
                        Call("coordinate", Id("x"), l)))))),
            AllMany([Variable("B", typeFamily), Variable("q", bonds),
                Variable("l", n), Variable("x", threads)],
                Equal(Call("pi", l, Id("x")), Call("coordinate", Id("x"), l))),
            telescope]);
    }

    private static Formula.BoundVariable Variable(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula AllMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula SomeMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula ConjunctionRows(params Formula[] terms)
    {
        var rows = new Formula[terms.Length];
        rows[0] = terms[0];
        for (var i = 1; i < terms.Length; i++)
            rows[i] = FormulaDsl.Seq(FormulaDsl.Land, FormulaDsl.Sp, terms[i]);
        return new Formula.Aligned([.. rows]);
    }
    private static Formula And(params Formula[] terms)
    {
        var result = terms[terms.Length - 1];
        for (var i = terms.Length - 2; i >= 0; i--)
            result = new Formula.Logic(terms[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Member(Formula value, Formula domain) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, domain);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Map(Formula law, Formula map) => Call("map", law, map);
    private static Formula Gap(Formula left, Formula right, Formula events) =>
        new Formula.Absolute(new Formula.Binary(Call("real", left, events),
            FormulaBinaryOperator.Subtract, Call("real", right, events)));
    private static Formula Comprehension(string variable, Formula domain, Formula predicate) =>
        FormulaDsl.Seq(FormulaDsl.OpenBrace, Member(Id(variable), domain), FormulaDsl.Mid,
            predicate, FormulaDsl.CloseBrace);
    private static Formula DependentProduct(string variable, Formula domain, Formula body) =>
        FormulaDsl.Seq(FormulaDsl.Prod, FormulaDsl.Underscore,
            FormulaDsl.Grp(Member(Id(variable), domain)), body);
    private static Formula Lambda(string variable, Formula domain, Formula body) =>
        FormulaDsl.Seq(FormulaDsl.Open, Id(variable), FormulaDsl.Colon, domain,
            FormulaDsl.Mapsto, body, FormulaDsl.Close);
    private static Formula Mixture(Formula left, Formula right) =>
        new Formula.Binary(
            new Formula.Binary(Call("ofReal", Id("t")), FormulaBinaryOperator.Multiply, Call("toMeasure", left)),
            FormulaBinaryOperator.Add,
            new Formula.Binary(Call("ofReal", new Formula.Binary(Num(1),
                FormulaBinaryOperator.Subtract, Id("t"))), FormulaBinaryOperator.Multiply, Call("toMeasure", right)));
}
