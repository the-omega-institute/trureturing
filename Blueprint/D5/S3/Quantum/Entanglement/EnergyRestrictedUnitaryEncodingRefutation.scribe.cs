using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class EnergyRestrictedUnitaryEncodingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/rochicarcellertavakoli2025energyentanglement");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four unitary encodings of a partially entangled state outperform every unassisted strategy at the same energy.",
        H("Unitary entanglement assistance under a vacuum energy restriction"), Blocks(
            Paragraph(Text(
                "Alice receives an input x, applies a unitary to her part of a shared pure state, "
                    + "and sends that part to Bob. Bob chooses a setting y and measures the joint system, "
                    + "obtaining an outcome b. This is the unitary case of the entanglement-assisted "
                    + "prepare-and-measure model in Section II, Eqs. (1)–(2), and Section IV.A. "
                    + "All sums range over the entire indicated finite type. Matrix entries are complex, "
                    + "probabilities and task values are real, and brackets denote anonymous typeclass assumptions.")),
            Node("IsPOVM", "Finite positive operator-valued measurements", PovmFormula(),
                "Every effect is positive semidefinite and the effects sum to the identity. "
                    + "The carrier n and outcome type B are finite; n also has decidable equality."),
            Node("UnitaryStrategy", "A pure state with local unitary encodings", UnitaryStrategyFormula(),
                "The squared moduli of the state coordinates sum to one. The type of U requires "
                    + "a unitary matrix on Alice's factor for every input. For every setting, Bob's "
                    + "effects form a POVM on the product of the two factors. These are the pure-state "
                    + "unitary strategies considered in Section IV.A."),
            Node("encoded", "The state after the message is encoded", EncodedFormula(),
                "Alice acts on her factor with U(x), while the identity acts on Bob's factor. "
                    + "The Kronecker product followed by matrix-vector multiplication gives the joint "
                    + "state received by Bob, specializing Eq. (1) to a unitary operation."),
            Node("unitaryProb", "The outcome probability of the joint measurement", UnitaryProbFormula(),
                "The real part of the quadratic form of M(y,b) on the encoded vector is the Born "
                    + "probability in Eq. (2). The conjugation in star is coordinatewise, and dotProduct "
                    + "sums products of matching coordinates. The expression is defined for arbitrary "
                    + "vectors and effects; UnitaryStrategy supplies their physical normalization."),
            Node("unitaryVacuum", "The vacuum component of the transmitted subsystem", UnitaryVacuumFormula(),
                "Sum the squared moduli of the encoded coordinates whose Alice index is zero. "
                    + "This is the vacuum population of the reduced message state. Equation (3) "
                    + "requires this quantity to be at least 1 − omega for every input, where omega "
                    + "is the allowed energy and NeZero dA makes the vacuum index available."),
            Node("QCStrategy", "Unassisted quantum communication with shared randomness", QCStrategyFormula(),
                "The finite random variable l has nonnegative weights q summing to one. Conditional "
                    + "on l and x, Alice sends a positive semidefinite trace-one matrix rho(l,x). "
                    + "Conditional on l and y, Bob measures a POVM. These are the states and measurements "
                    + "of the unassisted quantum model in Section II.B and Eq. (4). No entangled system "
                    + "is retained by Bob."),
            Node("qcProb", "Probabilities averaged over the shared random variable", QCProbFormula(),
                "Equation (4) averages the conditional Born probabilities with the weights q. "
                    + "The real part of the trace is explicit. The definition itself places no positivity "
                    + "or normalization conditions on the weights, states or effects."),
            Node("qcVacuum", "The averaged vacuum population", QCVacuumFormula(),
                "Equation (5) averages the vacuum entries of the conditional message states. "
                    + "The energy restriction is qcVacuum(q,rho,x) at least 1 − omega for each x. "
                    + "It constrains the average over l and permits the conditional energies to differ."),
            Node("taskValue", "A general finite linear communication task", TaskValueFormula(),
                "Each real coefficient c(b,x,y) multiplies the corresponding probability, and the "
                    + "sum includes all outcomes, inputs and settings. The coefficients are arbitrary; "
                    + "this includes success probabilities as well as other linear figures of merit."),
            Node("claim", "The positive answer to the question for general tasks", ClaimFormula(),
                "Section VI asks whether unitary encoding remains resourceless for general tasks. "
                    + "The displayed proposition is the positive answer for finite alphabets and "
                    + "0 ≤ omega < 1/2: every unitary entanglement-assisted value would be matched "
                    + "or exceeded by an unassisted strategy with the same energy bound. The latter "
                    + "may use any positive finite message dimension and any finite shared random variable. "
                    + "Result 4 concerns only probabilistic transmission of a bit; the proposition here "
                    + "quantifies over all finite linear tasks.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("energy-restricted-unitary-encoding-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Four messages give a strict advantage below half-unit energy"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(N("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take inputs and outcomes (u,v) in Fin 2 × Fin 2, one measurement setting, "
                            + "and task weights c(b,x,y) = 1/4 when b = x and zero otherwise. "
                            + "Alice and Bob share the pure state (4/5)|00⟩ + (3/5)|11⟩. "
                            + "Set Z = [[1,0],[0,−1]] and R = [[4/5,−3/5],[3/5,4/5]]. "
                            + "For input (u,v), Alice applies Z^u R Z^v. Bob measures the four rank-one "
                            + "projectors onto the orthonormal vectors "
                            + "m_(u,v) = (1/2)(1,−(−1)^v,(−1)^u,(−1)^(u+v)), "
                            + "in the coordinate order (00,01,10,11).")),
                    Paragraph(Text(
                        "For input (u,v), the encoded vector has coordinates "
                            + "(16/25,−(9/25)(−1)^v,(12/25)(−1)^u,(12/25)(−1)^(u+v)). "
                            + "Its vacuum component is 337/625 for every input. Thus the energy "
                            + "restriction holds with omega = 288/625 < 1/2. The overlap with the "
                            + "corresponding measurement vector is 49/50, giving task value 2401/2500.")),
                    Paragraph(Text(
                        "For every density matrix rho and effect 0 ≤ E ≤ I, "
                            + "Re Tr(E rho) − Re E_(0,0) ≤ sqrt(1 − Re rho_(0,0)). "
                            + "For a pure state, compression to the span of its vacuum and nonvacuum "
                            + "parts reduces this inequality to a two-dimensional Hermitian involution. "
                            + "Spectral decomposition and concavity of the square root give the density-matrix "
                            + "case. Summing the effect inequality over the four guesses and averaging "
                            + "over the shared random variable bounds every unassisted value for this "
                            + "task by 1/4 + sqrt(omega) under the same averaged energy restriction. "
                            + "Since sqrt(288/625) < 17/25, every such value is less than 93/100, "
                            + "whereas 2401/2500 > 93/100. Hence claim is false."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create("energy-restricted-unitary-encoding-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Q(string name)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(Operatorname);
            parts.Add(Grp(N(part)));
        }
        return Seq([.. parts]);
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula SomeInstance(Formula type, Formula body) =>
        Seq(Exists, Sp, OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Fin(string size) => Call("Fin", N(size));
    private static Formula Product() => Call("Prod", Fin("dA"), Fin("dB"));
    private static Formula Matrix(Formula carrier) => Call("Matrix", carrier, carrier, N("Complex"));
    private static Formula Vector() => Arrow(Product(), N("Complex"));
    private static Formula Unitaries() => Arrow(N("X"), Call("Matrix.unitaryGroup", Fin("dA"), N("Complex")));
    private static Formula JointEffects() => Arrow(N("Y"), Arrow(N("B"), Matrix(Product())));
    private static Formula Weights() => Arrow(N("L"), N("Real"));
    private static Formula Messages() => Arrow(N("L"), Arrow(N("X"), Matrix(Fin("d"))));
    private static Formula QCEffects() => Arrow(N("L"), Arrow(N("Y"), Arrow(N("B"), Matrix(Fin("d")))));
    private static Formula Behaviours() => Arrow(N("B"), Arrow(N("X"), Arrow(N("Y"), N("Real"))));
    private static Formula Positive(Formula value) => Call("Matrix.PosSemidef", value);
    private static Formula Trace(Formula value) => Call("Matrix.trace", value);
    private static Formula RealPart(Formula value) => Call("Complex.re", value);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(N(name), Colon, type)), Parenthesized(body));
    private static Formula Types(Formula body) =>
        All("X", N("Type"), All("Y", N("Type"), All("B", N("Type"), body)));
    private static Formula Dimensions(Formula body) => All("dA", N("Nat"), All("dB", N("Nat"), body));
    private static Formula UnitaryData(Formula body) =>
        All("Psi", Vector(), All("U", Unitaries(), All("M", JointEffects(), body)));
    private static Formula QCData(Formula body) =>
        All("q", Weights(), All("rho", Messages(), All("M", QCEffects(), body)));
    private static Formula Encoded() => Call("encoded", N("Psi"), N("U"), N("x"));
    private static Formula Energy(Formula vacuum) => All("x", N("X"), Le(Sub(D(1), N("omega")), vacuum));

    private static Formula PovmFormula() => All("n", N("Type"), All("B", N("Type"),
        Instance(Call("Fintype", N("n")), Instance(Call("DecidableEq", N("n")),
        Instance(Call("Fintype", N("B")), All("M", Arrow(N("B"), Matrix(N("n"))),
            IffFormula(Call("IsPOVM", N("M")), And(
                All("b", N("B"), Positive(At(N("M"), N("b")))),
                Eq(SumOver("b", N("B"), At(N("M"), N("b"))), D(1))))))))));

    private static Formula UnitaryStrategyFormula() => Types(Instance(Call("Fintype", N("B")),
        Dimensions(UnitaryData(IffFormula(Call("UnitaryStrategy", N("Psi"), N("U"), N("M")),
            And(Eq(SumOver("i", Product(), Call("Complex.normSq", At(N("Psi"), N("i")))), D(1)),
                All("y", N("Y"), Call("IsPOVM", At(N("M"), N("y"))))))))));

    private static Formula EncodedFormula() => All("X", N("Type"), Dimensions(
        All("Psi", Vector(), All("U", Unitaries(), All("x", N("X"),
            Eq(Encoded(), Call("Matrix.mulVec",
                Call("Matrix.kronecker", Typed(At(N("U"), N("x")), Matrix(Fin("dA"))),
                    Typed(D(1), Matrix(Fin("dB")))), N("Psi"))))))));

    private static Formula UnitaryProbFormula() => Types(Dimensions(UnitaryData(
        All("b", N("B"), All("x", N("X"), All("y", N("Y"),
            Eq(Call("unitaryProb", N("Psi"), N("U"), N("M"), N("b"), N("x"), N("y")),
                RealPart(Call("dotProduct", Call("star", Encoded()),
                    Call("Matrix.mulVec", At(N("M"), N("y"), N("b")), Encoded()))))))))));

    private static Formula UnitaryVacuumFormula() => All("X", N("Type"), Dimensions(
        Instance(Call("NeZero", N("dA")), All("Psi", Vector(), All("U", Unitaries(), All("x", N("X"),
            Eq(Call("unitaryVacuum", N("Psi"), N("U"), N("x")),
                SumOver("j", Fin("dB"), new Formula.Power(
                    Parenthesized(Seq(Vert, At(Encoded(), Call("Prod.mk", D(0), N("j"))), Vert)), D(2))))))))));

    private static Formula QCStrategyFormula()
    {
        var state = At(N("rho"), N("l"), N("x"));
        var effect = At(N("M"), N("l"), N("y"), N("b"));
        var conditions = And(All("l", N("L"), Le(D(0), At(N("q"), N("l")))),
            And(Eq(SumOver("l", N("L"), At(N("q"), N("l"))), D(1)),
                And(All("l", N("L"), All("x", N("X"), And(Positive(state), Eq(Trace(state), D(1))))),
                    All("l", N("L"), All("y", N("Y"), And(
                        All("b", N("B"), Positive(effect)), Eq(SumOver("b", N("B"), effect), D(1))))))));
        return Types(All("L", N("Type"), Instance(Call("Fintype", N("B")),
            Instance(Call("Fintype", N("L")), All("d", N("Nat"), QCData(
                IffFormula(Call("QCStrategy", N("q"), N("rho"), N("M")), conditions)))))));
    }

    private static Formula QCProbFormula() => Types(All("L", N("Type"),
        Instance(Call("Fintype", N("L")), All("d", N("Nat"), QCData(
            All("b", N("B"), All("x", N("X"), All("y", N("Y"),
                Eq(Call("qcProb", N("q"), N("rho"), N("M"), N("b"), N("x"), N("y")),
                    SumOver("l", N("L"), Mul(At(N("q"), N("l")),
                        RealPart(Trace(Mul(At(N("rho"), N("l"), N("x")),
                            At(N("M"), N("l"), N("y"), N("b"))))))))))))))));

    private static Formula QCVacuumFormula() => All("X", N("Type"), All("L", N("Type"),
        Instance(Call("Fintype", N("L")), All("d", N("Nat"), Instance(Call("NeZero", N("d")),
            All("q", Weights(), All("rho", Messages(), All("x", N("X"),
                Eq(Call("qcVacuum", N("q"), N("rho"), N("x")), SumOver("l", N("L"),
                    Mul(At(N("q"), N("l")), RealPart(At(N("rho"), N("l"), N("x"), D(0), D(0))))))))))))));

    private static Formula TaskValueFormula() => Types(Instance(Call("Fintype", N("X")),
        Instance(Call("Fintype", N("Y")), Instance(Call("Fintype", N("B")),
            All("c", Behaviours(), All("p", Behaviours(), Eq(Call("taskValue", N("c"), N("p")),
                SumOver("b", N("B"), SumOver("x", N("X"), SumOver("y", N("Y"),
                    Mul(At(N("c"), N("b"), N("x"), N("y")), At(N("p"), N("b"), N("x"), N("y")))))))))))));

    private static Formula ClaimFormula()
    {
        var unassisted = Some("d", N("Nat"), SomeInstance(Call("NeZero", N("d")),
            Some("L", N("Type"), SomeInstance(Call("Fintype", N("L")),
                Some("q", Weights(), Some("rho", Messages(), Some("N", QCEffects(),
                    And(Call("QCStrategy", N("q"), N("rho"), N("N")),
                        And(Energy(Call("qcVacuum", N("q"), N("rho"), N("x"))),
                            Le(Call("taskValue", N("c"), Call("unitaryProb", N("Psi"), N("U"), N("M"))),
                                Call("taskValue", N("c"), Call("qcProb", N("q"), N("rho"), N("N")))))))))))));
        var comparison = Imp(Call("UnitaryStrategy", N("Psi"), N("U"), N("M")),
            Imp(Energy(Call("unitaryVacuum", N("Psi"), N("U"), N("x"))), unassisted));
        return IffFormula(N("claim"), Types(Instance(Call("Fintype", N("X")),
            Instance(Call("Fintype", N("Y")), Instance(Call("Fintype", N("B")),
                All("c", Behaviours(), All("omega", N("Real"), Imp(Le(D(0), N("omega")),
                    Imp(Lt(N("omega"), new Formula.Fraction(D(1), D(2))),
                        Dimensions(Instance(Call("NeZero", N("dA")), UnitaryData(comparison))))))))))));
    }
}
