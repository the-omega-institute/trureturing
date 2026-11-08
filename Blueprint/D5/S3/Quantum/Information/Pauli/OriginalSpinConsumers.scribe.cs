using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.Pauli;

internal sealed class OriginalSpinConsumersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/Pauli/OriginalSpinConsumers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both Pauli multiplication orders on the original real spin carrier.",
        H("Original spin evaluations and Pauli products"),
        Blocks(
            Def("E", "Original carrier", Equal(E(), Call("Prod", R(), V())),
                "The carrier is the canonical OriginalDContract carrier E = R x (Fin 3 -> R). Write a = (s,x); this source consumes that exact carrier."),
            Def("unit", "Unit", Equal(U(), Pair(Num(1), Num(0))),
                "The unit has scalar coordinate one and vector coordinate zero."),
            Def("toFamily", "Four-coordinate transport", CoordinateFormula(true),
                "The existing spin-product carrier orders the canonical vector coordinates as scalar, x, y, z. This map is the supplier transport from the canonical carrier."),
            Def("ofFamily", "Scalar and vector transport", CoordinateFormula(false),
                "The inverse coordinate transport returns the original scalar and function-valued vector coordinates."),
            Def("jordan", "Original Jordan product", JordanFormula(),
                "The product is definitionally the canonical OriginalDContract.jordan; jordan_supplier records its correspondence with PauliFixedProductFamily.S."),
            Def("cross", "Bilinear cross channel", CrossFormula(),
                "The channel transports PauliFixedProductFamily.C to the canonical OriginalDContract.cross channel and discards both scalar coordinates."),
            Def("sign", "Global orientation", For(Equal(Call("sign", X("o")),
                Call("ite", X("o"), Num(1), Negate(Num(1)))), ("o", X("Bool"))),
                "False selects sign minus one. True selects sign plus one."),
            Def("fixed", "Fixed original relation", For(EachE(Equal(Fixed(X("o"), X("a"), X("b")),
                Smul(Call("sign", X("o")), Call("cross", X("a"), X("b")))), "a", "b"), ("o", X("Bool"))),
                "One orientation is selected for the entire relation, independently of inputs and evaluations."),
            Def("originalNorm", "Original norm", EachE(Equal(N(X("a")),
                Add(Call("abs", S(X("a"))), Call("vnorm", VPart(X("a"))))), "a"),
                "This is the exact OriginalDContract norm |s| + vnorm x."),
            Def("cone", "Original cone", EachE(Iff(Call("cone", X("a")),
                LE(Call("vnorm", VPart(X("a"))), S(X("a")))), "a"),
                "Positivity is the exact OriginalDContract cone inequality vnorm x <= s."),
            Def("evaluate", "All-mass evaluations", AllMV(EachE(Equal(Eval(X("a")),
                Add(Multiply(X("m"), S(X("a"))), Inner(X("v"), VPart(X("a"))))), "a")),
                "The raw matrix coordinates represent every canonical Evaluation mass m and vector v with vnorm v <= m, including zero, subnormalized and unequal masses."),
            Def("PositiveEvaluation", "Positive real linear functionals", For(
                Iff(Call("PositiveEvaluation", X("alpha")), EachE(
                    Implies(Call("cone", X("a")), LE(Num(0), Apply(X("alpha"), X("a")))), "a")),
                ("alpha", Linear())), "A real linear functional is positive on the entire original spin cone."),
            Def("evaluationLinear", "Linear evaluation map", AllMV(EachE(Equal(
                Apply(Call("evaluationLinear", X("m"), X("v")), X("a")), Eval(X("a"))), "a")),
                "The evaluation formula is real linear before imposing positivity."),
            Def("phi", "Pauli observable", EachE(Equal(Phi(X("a")),
                Call("scalarB", S(X("a")), Call("toLp", Num(2), VPart(X("a"))))), "a"),
                "The supplier scalarB gives the Hermitian matrix s I plus x dot sigma."),
            Def("density", "Unnormalized density", AllMV(Equal(Rho(),
                Smul(Typed(Fraction(Num(1), Num(2)), C()),
                    Call("scalarB", X("m"), Call("toLp", Num(2), X("v"))))),
                "The density has trace m and is positive exactly when norm v is at most m."),
            Def("product", "Both matrix orientations", For(Equal(
                Call("product", X("o"), X("A"), X("B")),
                Call("ite", X("o"), Multiply(X("B"), X("A")), Multiply(X("A"), X("B")))),
                ("o", X("Bool")), ("A", Mat()), ("B", Mat())),
                "False uses ordinary multiplication. True uses the opposite order."),
            Def("gram", "Actual directed Gram table", GramFormula(),
                "Every ordered pair uses the actual D value, including each diagonal and both directed off-diagonal entries."),
            Def("P2", "Two-label complex positivity", For(Iff(Call("P2", X("D")),
                Call("OriginalDContract.P2", X("D"))), ("D", Rel())),
                "This node is an alias of OriginalDContract.P2: every canonical positive Evaluation and every original pair uses the same total D in both directed off-diagonal entries and on both diagonals."),
            Def("PB", "Original plus/minus balance", For(Iff(Call("PB", X("D")),
                Call("OriginalDContract.PB", X("D"))), ("D", Rel())),
                "This node is an alias of OriginalDContract.PB: the canonical phaseR/phaseS outer pairs at t = +1 and t = -1 are compared with the same D."),
            Def("OriginalContinuous", "Continuity in the original norm", For(
                Iff(Call("OriginalContinuous", X("D")), Continuity()), ("D", Rel())),
                "Input and output increments are measured by |s| plus norm x."),
            Def("Consequences", "Same-relation consequences", For(
                Iff(Call("Consequences", X("D")), ConsequenceFormula()), ("D", Rel())),
                "Every conclusion concerns the same arbitrary total relation D on the canonical OriginalDContract carrier, including the original reassociation identity."),
            Def("MatrixInterfaces", "Original cone, norm and evaluation interfaces", For(
                Iff(Call("MatrixInterfaces", X("o"), X("D")), InterfaceFormula()),
                ("o", X("Bool")), ("D", Rel())),
                "Every positive original linear functional and every positive two by two matrix is represented with its full canonical mass and vector. The matrix order interval retains the exact OriginalDContract norm."),
            Node("same_D_consequences", "One global orientation supplies all consumers", DescribeRole.Theorem,
                For(Implies(EachE(Equal(DApply(X("a"), X("b")),
                    CrossD(X("o"), X("a"), X("b"))), "a", "b"),
                    And(Call("Consequences", X("D")), Call("MatrixInterfaces", X("o"), X("D")))),
                    ("o", X("Bool")), ("D", Rel())),
                "The hypothesis is the canonical OriginalDContract.crossD orientation on every original input; fixed_crossD connects it to one Bool-selected Pauli multiplication order. For ordinary order the complex Gram quadratic form is tr(rho Z* Z), with Z the finite sum of Hermitian labels with arbitrary complex coefficients. Cyclicity gives tr(Z rho Z*), which is nonnegative. Opposite order transposes the same directed Gram table. The canonical PB and reassociation, original-norm bounds, continuity, all-mass evaluation interfaces and all finite Gram consequences are then supplied for this same D. No argument divides by the mass; this endpoint is conditional and does not classify an arbitrary D.")),
        [])));

    private static Formula CoordinateFormula(bool forward)
    {
        var a = X("a");
        if (forward)
        {
            var coords = Seq(Open, S(a), Comma, Entry(VPart(a), 0), Comma,
                Entry(VPart(a), 1), Comma, Entry(VPart(a), 2), Close);
            return EachE(Equal(Call("toFamily", a), Call("toLp", Num(2), coords)), "a");
        }
        var vector = For(Equal(Apply(VPart(a), X("i")), Entry(a, 0)), ("i", Fin(3)));
        return For(Equal(Call("ofFamily", a), Pair(Entry(a, 0), vector)),
            ("a", Call("Pi", Fin(4), R())));
    }

    private static Formula JordanFormula()
    {
        var a = X("a"); var b = X("b");
        var scalar = Add(Multiply(S(a), S(b)), Call("OriginalDContract.dot", VPart(a), VPart(b)));
        var vector = Add(Smul(S(a), VPart(b)), Smul(S(b), VPart(a)));
        return EachE(Equal(J(a, b), Pair(scalar, vector)), "a", "b");
    }

    private static Formula CrossFormula()
    {
        var vector = Call("OriginalDContract.cross", VPart(X("a")), VPart(X("b")));
        return EachE(Equal(Call("cross", X("a"), X("b")), Pair(Num(0), vector)), "a", "b");
    }

    private static Formula GramFormula()
    {
        var a = Apply(X("a"), X("i")); var b = Apply(X("a"), X("j"));
        var entry = Subtract(Typed(Eval(J(a, b)), C()), Multiply(Imag(), Typed(Eval(DApply(a, b)), C())));
        return For(AllMV(For(Equal(Apply(Gram(), X("i"), X("j")), entry),
            ("a", Arrow(X("I"), E())), ("i", X("I")), ("j", X("I")))), ("I", X("Type")), ("D", Rel()));
    }

    private static Formula ConsequenceFormula()
    {
        var a = X("a"); var b = X("b"); var c = X("c");
        var a1 = X("a1"); var b1 = X("b1"); var r = X("r"); var q = X("q");
        var leftZero = For(EachE(Equal(DApply(Smul(r, U()), b), Num(0)), "b"), ("r", R()));
        var rightZero = For(EachE(Equal(DApply(a, Smul(r, U())), Num(0)), "a"), ("r", R()));
        var translation = For(EachE(Equal(DApply(Add(a, Smul(r, U())), Add(b, Smul(q, U()))), DApply(a, b)),
            "a", "b"), ("r", R()), ("q", R()));
        var addLeft = EachE(Equal(DApply(Add(a, b), c), Add(DApply(a, c), DApply(b, c))), "a", "b", "c");
        var addRight = EachE(Equal(DApply(a, Add(b, c)), Add(DApply(a, b), DApply(a, c))), "a", "b", "c");
        var smulLeft = For(EachE(Equal(DApply(Smul(r, a), b), Smul(r, DApply(a, b))), "a", "b"), ("r", R()));
        var smulRight = For(EachE(Equal(DApply(a, Smul(r, b)), Smul(r, DApply(a, b))), "a", "b"), ("r", R()));
        var bound = EachE(LE(N(DApply(a, b)), Multiply(N(a), N(b))), "a", "b");
        var difference = EachE(LE(N(Subtract(DApply(a, b), DApply(a1, b1))),
            Add(Multiply(N(Subtract(a, a1)), N(b)), Multiply(N(a1), N(Subtract(b, b1))))), "a", "b", "a1", "b1");
        var finite = For(PositiveMV(For(PSD(Gram()), ("a", Arrow(Call("Fin", X("n")), E())))), ("n", X("Nat")));
        var reassociation = EachE(Equal(Subtract(J(J(a, b), c), J(a, J(b, c))),
            Subtract(DApply(DApply(a, b), c), DApply(a, DApply(b, c)))), "a", "b", "c");
        return Conjoin(Call("P2", X("D")), Call("PB", X("D")), leftZero, rightZero, translation,
            addLeft, addRight, smulLeft, smulRight, bound, difference, Call("OriginalContinuous", X("D")), finite, reassociation);
    }

    private static Formula InterfaceFormula()
    {
        var a = X("a"); var b = X("b"); var r = X("r"); var alpha = X("alpha");
        var parameterBound = LE(Call("vnorm", X("v")), X("m"));
        var positive = AllMV(Iff(PSD(Rho()), parameterBound));
        var mass = AllMV(Equal(Trace(Rho()), Typed(X("m"), C())));
        var evaluationPositive = AllMV(Iff(Call("PositiveEvaluation", Call("evaluationLinear", X("m"), X("v"))), parameterBound));
        var evaluationComplete = For(Implies(Call("PositiveEvaluation", alpha),
            Exists(And(parameterBound, EachE(Equal(Apply(alpha, a), Eval(a)), "a")), ("m", R()), ("v", V()))), ("alpha", Linear()));
        var pairing = AllMV(EachE(Equal(Trace(Multiply(Rho(), Phi(a))), Typed(Eval(a), C())), "a"));
        var cone = EachE(Iff(PSD(Phi(a)), Call("cone", a)), "a");
        var scalarIdentity = Smul(Typed(r, C()), Typed(Num(1), Mat()));
        var interval = EachE(For(Iff(And(PSD(Subtract(scalarIdentity, Phi(a))), PSD(Add(scalarIdentity, Phi(a)))),
            LE(N(a), r)), ("r", R())), "a");
        var densityComplete = For(Implies(PSD(X("rho")),
            Exists(And(parameterBound, Equal(X("rho"), Rho())), ("m", R()), ("v", V()))), ("rho", Mat()));
        var multiplication = EachE(Equal(Call("product", X("o"), Phi(a), Phi(b)),
            Subtract(Phi(J(a, b)), Smul(Imag(), Phi(DApply(a, b))))), "a", "b");
        return Conjoin(positive, mass, evaluationPositive, evaluationComplete, pairing, cone, interval, densityComplete, multiplication);
    }

    private static Formula Continuity()
    {
        var a = X("a"); var b = X("b"); var a1 = X("a1"); var b1 = X("b1");
        var eta = X("eta"); var delta = X("delta");
        var increment = N(Subtract(DApply(a1, b1), DApply(a, b)));
        var local = EachE(Implies(LT(N(Subtract(a1, a)), delta),
            Implies(LT(N(Subtract(b1, b)), delta), LT(increment, eta))), "a1", "b1");
        return EachE(For(Implies(LT(Num(0), eta), Exists(And(LT(Num(0), delta), local), ("delta", R()))),
            ("eta", R())), "a", "b");
    }

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Node(name, title, DescribeRole.Definition, formula, prose);
    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("original-spin-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string s) => F.Id(s);
    private static Formula R() => Seq(Mathbb, Grp(X("R")));
    private static Formula C() => Seq(Mathbb, Grp(X("C")));
    private static Formula Imag() => Seq(Operatorname, Grp(X("Complex"), Dot, X("I")));
    private static Formula E() => X("E");
    private static Formula V() => Arrow(Fin(3), R());
    private static Formula Mat() => Call("Matrix", Fin(2), Fin(2), C());
    private static Formula Rel() => Arrow(E(), Arrow(E(), E()));
    private static Formula Linear() => Call("LinearMap", R(), E(), R());
    private static Formula Fin(byte n) => Call("Fin", Num(n));
    private static Formula U() => X("unit");
    private static Formula S(Formula a) => Call("fst", a);
    private static Formula VPart(Formula a) => Call("snd", a);
    private static Formula Entry(Formula a, byte n) => Apply(a, Num(n));
    private static Formula J(Formula a, Formula b) => Call("jordan", a, b);
    private static Formula DApply(Formula a, Formula b) => Apply(X("D"), a, b);
    private static Formula Fixed(Formula o, Formula a, Formula b) => Call("fixed", o, a, b);
    private static Formula CrossD(Formula o, Formula a, Formula b) =>
        Call("OriginalDContract.crossD", Call("if", o, X(".plus"), X(".minus")), a, b);
    private static Formula N(Formula a) => Call("originalNorm", a);
    private static Formula Eval(Formula a) => Call("evaluate", X("m"), X("v"), a);
    private static Formula Phi(Formula a) => Call("phi", a);
    private static Formula Rho() => Call("density", X("m"), X("v"));
    private static Formula Gram() => Call("gram", X("D"), X("m"), X("v"), X("a"));
    private static Formula Inner(Formula a, Formula b) => Call("OriginalDContract.dot", a, b);
    private static Formula PSD(Formula a) => Call("PosSemidef", a);
    private static Formula Trace(Formula a) => Call("trace", a);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Typed(Formula a, Formula t) => Seq(Open, a, Colon, Sp, t, Close);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula For(Formula body, params (string Name, Formula Type)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; --i)
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variables[i].Name), variables[i].Type, body);
        return body;
    }
    private static Formula Exists(Formula body, params (string Name, Formula Type)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; --i)
            body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variables[i].Name), variables[i].Type, body);
        return body;
    }
    private static Formula EachE(Formula body, params string[] names)
    {
        for (var i = names.Length - 1; i >= 0; --i) body = For(body, (names[i], E()));
        return body;
    }
    private static Formula AllMV(Formula body) => For(body, ("m", R()), ("v", V()));
    private static Formula PositiveMV(Formula body) => AllMV(Implies(LE(Call("vnorm", X("v")), X("m")), body));
    private static Formula Conjoin(params Formula[] formulas)
    {
        var result = formulas[^1];
        for (var i = formulas.Length - 2; i >= 0; --i) result = And(formulas[i], result);
        return result;
    }
    private static Formula Call(string name, params Formula[] args) => Apply(Seq(Operatorname, Grp(X(name))), args);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Smul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Cdot, Sp, Open, b, Close);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
