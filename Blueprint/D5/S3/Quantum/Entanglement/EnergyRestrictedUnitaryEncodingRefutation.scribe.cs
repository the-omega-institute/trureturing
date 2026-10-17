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
                    + "All finite sums range over the entire indicated finite type; each tsum ranges over its indicated arbitrary index type. Matrix entries are complex, "
                    + "probabilities and task values are real, and brackets denote anonymous typeclass assumptions.")),
            Node("IsPOVM", "Finite positive operator-valued measurements", PovmFormula(),
                "Every effect is positive semidefinite and the effects sum to the identity. "
                    + "The carrier n and outcome type B are finite; n also has decidable equality."),
            Node("UnitaryStrategy", "A pure state with local unitary encodings", UnitaryStrategyFormula(),
                "The squared moduli of the state coordinates sum to one. The type of U requires "
                    + "a unitary matrix on Alice's factor for every input. For every setting, Bob's "
                    + "effects form a POVM on the product of the two factors. These are the pure-state "
                    + "unitary strategies considered in Section IV.A.", AssessedProvenance.FromLiterature(Source)),
            Node("encoded", "The state after the message is encoded", EncodedFormula(),
                "Alice acts on her factor with U(x), while the identity acts on Bob's factor. "
                    + "The Kronecker product followed by matrix-vector multiplication gives the joint "
                    + "state received by Bob, specializing Eq. (1) to a unitary operation.", AssessedProvenance.FromLiterature(Source)),
            Node("unitaryProb", "The outcome probability of the joint measurement", UnitaryProbFormula(),
                "The real part of the quadratic form of M(y,b) on the encoded vector is the Born "
                    + "probability in Eq. (2). The conjugation in star is coordinatewise, and dotProduct "
                    + "sums products of matching coordinates. The expression is defined for arbitrary "
                    + "vectors and effects; UnitaryStrategy supplies their physical normalization.", AssessedProvenance.FromLiterature(Source)),
            Node("unitaryVacuum", "The vacuum component of the transmitted subsystem", UnitaryVacuumFormula(),
                "Sum the squared moduli of the encoded coordinates whose Alice index is zero. "
                    + "This is the vacuum population of the reduced message state. Equation (3) "
                    + "requires this quantity to be at least 1 − omega for every input, where omega "
                    + "is the allowed energy and NeZero dA makes the vacuum index available.", AssessedProvenance.FromLiterature(Source)),
            Node("QCStrategy", "Unassisted quantum communication with shared randomness", QCStrategyFormula(),
                "The message space H is an arbitrary complex Hilbert space with unit vacuum vector vac; "
                    + "there is no dimension restriction. Shared randomness ranges over an arbitrary type L, "
                    + "with nonnegative weights q and HasSum q 1. For each l and x, density operators enter "
                    + "through their ensemble decompositions: nonnegative weights p(l,x,k) with sum one "
                    + "and unit vectors psi(l,x,k), indexed by an arbitrary type K. Spectral decomposition "
                    + "represents every density operator in this way. For each l and y, N is a finite POVM "
                    + "of bounded complex linear operators; 0 ≤ N means positivity in the operator order. "
                    + "These are the states and measurements of the unassisted quantum model in Section II.B "
                    + "and Eq. (4). Bob retains no entangled system.", AssessedProvenance.FromLiterature(Source)),
            Node("qcProb", "Probabilities averaged over the shared random variable", QCProbFormula(),
                "Equation (4) averages the Born probabilities first over each message ensemble and then "
                    + "over shared randomness. For a density operator rho represented by an ensemble, "
                    + "Re Tr(N rho) is the weighted sum of Re inner(Complex,psi,N psi). The two tsum "
                    + "expressions range over the entire arbitrary index types L and K. The definition "
                    + "requires a complex inner-product space; positivity, normalization and completeness "
                    + "are supplied separately by QCStrategy.", AssessedProvenance.FromLiterature(Source)),
            Node("qcVacuum", "The averaged vacuum population", QCVacuumFormula(),
                "Equation (5) averages the squared vacuum overlaps over each message ensemble and "
                    + "over shared randomness, using tsum on both arbitrary index types. For unit vac, "
                    + "the ensemble average is the vacuum population of the corresponding density operator. "
                    + "The energy restriction is qcVacuum(vac,q,p,psi,x) at least 1 − omega for each x. "
                    + "It permits the conditional energies to differ. This expression is defined on any "
                    + "complex inner-product space without normalization assumptions.", AssessedProvenance.FromLiterature(Source)),
            Node("taskValue", "A general finite linear communication task", TaskValueFormula(),
                "Each real coefficient c(b,x,y) multiplies the corresponding probability, and the "
                    + "sum includes all outcomes, inputs and settings. The coefficients are arbitrary; "
                    + "this includes success probabilities as well as other linear figures of merit."),
            Node("claim", "The positive answer to the question for general tasks", ClaimFormula(),
                "Section VI asks whether unitary encoding remains resourceless for general tasks. "
                    + "The displayed proposition is the positive answer for finite alphabets and "
                    + "0 ≤ omega < 1/2: every unitary entanglement-assisted value would be matched "
                    + "or exceeded by an unassisted strategy with the same energy bound. The latter "
                    + "may use any complex Hilbert message space with a unit vacuum vector, arbitrary "
                    + "shared randomness, density operators represented by ensembles, and POVMs of positive "
                    + "bounded operators. Its message dimension has no restriction. "
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
                        "In every complex Hilbert space, unit vectors g and psi and an effect 0 ≤ E ≤ I "
                            + "satisfy Delta = Re inner(psi,E psi) − Re inner(g,E g) "
                            + "≤ sqrt(1 − |inner(g,psi)|²). Multiply psi by a complex scalar of modulus one "
                            + "so that a = inner(g,psi) is real and nonnegative, and put u = psi + g and "
                            + "v = psi − g. Then Delta "
                            + "is both Re inner(u,E v) and −Re inner(u,(I − E)v). Cauchy–Schwarz for the "
                            + "positive forms of E and I − E gives Delta² ≤ A B and "
                            + "Delta² ≤ (U − A)(V − B), where A = inner(u,E u), B = inner(v,E v), "
                            + "U = norm(u)² = 2 + 2a and V = norm(v)² = 2 − 2a. The inequality "
                            + "sqrt(A B) + sqrt((U − A)(V − B)) ≤ sqrt(U V) yields the stated bound.")),
                    Paragraph(Text(
                        "For nonnegative weights w summing to one and 0 ≤ t_j ≤ 1, put s = sum_j w_j t_j. "
                            + "Cauchy–Schwarz for sqrt(w_j) and sqrt(w_j t_j) gives "
                            + "sum_j w_j sqrt(t_j) = sum_j sqrt(w_j)·sqrt(w_j t_j) "
                            + "≤ sqrt(sum_j w_j)·sqrt(sum_j w_j t_j) = sqrt(s). "
                            + "Apply this averaging bound to the ensemble decompositions "
                            + "of the density operators and then to shared randomness. The POVM identity gives "
                            + "sum_x inner(vac,N_x vac) = 1 for each value of the shared random variable. "
                            + "Consequently, in every Hilbert message space the four-guess task value is at most "
                            + "1/4 + (1/4) sum_x sqrt(1 − qcVacuum(vac,q,p,psi,x)) ≤ 1/4 + sqrt(omega) "
                            + "under the same averaged energy restriction. "
                            + "Since sqrt(288/625) < 17/25, every such value is less than 93/100, "
                            + "whereas 2401/2500 > 93/100. Hence claim is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("roch-i-carceller-tavakoli-2025-energy-restricted-unitary-encoding"),
                    ResolutionKind.Refuted))
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
    private static Formula EnsembleWeights() => Arrow(N("L"), Arrow(N("X"), Arrow(N("K"), N("Real"))));
    private static Formula Messages() => Arrow(N("L"), Arrow(N("X"), Arrow(N("K"), N("H"))));
    private static Formula Operators() => Call("ContinuousLinearMap", N("Complex"), N("H"), N("H"));
    private static Formula QCEffects() => Arrow(N("L"), Arrow(N("Y"), Arrow(N("B"), Operators())));
    private static Formula Behaviours() => Arrow(N("B"), Arrow(N("X"), Arrow(N("Y"), N("Real"))));
    private static Formula Positive(Formula value) => Call("Matrix.PosSemidef", value);
    private static Formula RealPart(Formula value) => Call("Complex.re", value);
    private static Formula Inner(Formula left, Formula right) => Call("inner", N("Complex"), left, right);
    private static Formula NormSquared(Formula value) => new Formula.Power(new Formula.Norm(value), D(2));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(N(name), Colon, type)), Parenthesized(body));
    private static Formula TsumOver(string name, Formula type, Formula body) =>
        Call("tsum", Seq(Typed(N(name), type), Sp, Mapsto, Sp, body));
    private static Formula HilbertInstances(Formula body, bool complete = false) =>
        Instance(Call("NormedAddCommGroup", N("H")),
            Instance(Call("InnerProductSpace", N("Complex"), N("H")),
                complete ? Instance(Call("CompleteSpace", N("H")), body) : body));
    private static Formula Types(Formula body) =>
        All("X", N("Type"), All("Y", N("Type"), All("B", N("Type"), body)));
    private static Formula Dimensions(Formula body) => All("dA", N("Nat"), All("dB", N("Nat"), body));
    private static Formula UnitaryData(Formula body) =>
        All("Psi", Vector(), All("U", Unitaries(), All("M", JointEffects(), body)));
    private static Formula EnsembleData(Formula body) =>
        All("q", Weights(), All("p", EnsembleWeights(), All("psi", Messages(), body)));
    private static Formula QCData(Formula body) => EnsembleData(All("N", QCEffects(), body));
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
        var vector = At(N("psi"), N("l"), N("x"), N("k"));
        var effect = At(N("N"), N("l"), N("y"), N("b"));
        var effects = All("l", N("L"), All("y", N("Y"), And(
            All("b", N("B"), Le(D(0), effect)), Eq(SumOver("b", N("B"), effect), D(1)))));
        var unitVectors = All("l", N("L"), All("x", N("X"), All("k", N("K"),
            Eq(new Formula.Norm(vector), D(1)))));
        var ensembleSums = All("l", N("L"), All("x", N("X"),
            Call("HasSum", At(N("p"), N("l"), N("x")), D(1))));
        var ensemblePositive = All("l", N("L"), All("x", N("X"), All("k", N("K"),
            Le(D(0), At(N("p"), N("l"), N("x"), N("k"))))));
        var conditions = And(Eq(new Formula.Norm(N("vac")), D(1)),
            And(All("l", N("L"), Le(D(0), At(N("q"), N("l")))),
                And(Call("HasSum", N("q"), D(1)),
                    And(ensemblePositive, And(ensembleSums, And(unitVectors, effects))))));
        var body = All("vac", N("H"), QCData(
            IffFormula(Call("QCStrategy", N("vac"), N("q"), N("p"), N("psi"), N("N")), conditions)));
        return Types(All("H", N("Type"), All("L", N("Type"), All("K", N("Type"),
            Instance(Call("Fintype", N("B")), HilbertInstances(body, complete: true))))));
    }

    private static Formula QCProbFormula()
    {
        var vector = At(N("psi"), N("l"), N("x"), N("k"));
        var average = TsumOver("l", N("L"), Mul(At(N("q"), N("l")),
            TsumOver("k", N("K"), Mul(At(N("p"), N("l"), N("x"), N("k")),
                RealPart(Inner(vector, At(At(N("N"), N("l"), N("y"), N("b")), vector)))))));
        var body = QCData(All("b", N("B"), All("x", N("X"), All("y", N("Y"),
            Eq(Call("qcProb", N("q"), N("p"), N("psi"), N("N"), N("b"), N("x"), N("y")), average)))));
        return Types(All("H", N("Type"), All("L", N("Type"), All("K", N("Type"),
            HilbertInstances(body)))));
    }

    private static Formula QCVacuumFormula()
    {
        var average = TsumOver("l", N("L"), Mul(At(N("q"), N("l")),
            TsumOver("k", N("K"), Mul(At(N("p"), N("l"), N("x"), N("k")),
                NormSquared(Inner(N("vac"), At(N("psi"), N("l"), N("x"), N("k"))))))));
        var body = All("vac", N("H"), EnsembleData(All("x", N("X"),
            Eq(Call("qcVacuum", N("vac"), N("q"), N("p"), N("psi"), N("x")), average))));
        return All("X", N("Type"), All("H", N("Type"), All("L", N("Type"), All("K", N("Type"),
            HilbertInstances(body)))));
    }

    private static Formula TaskValueFormula() => Types(Instance(Call("Fintype", N("X")),
        Instance(Call("Fintype", N("Y")), Instance(Call("Fintype", N("B")),
            All("c", Behaviours(), All("p", Behaviours(), Eq(Call("taskValue", N("c"), N("p")),
                SumOver("b", N("B"), SumOver("x", N("X"), SumOver("y", N("Y"),
                    Mul(At(N("c"), N("b"), N("x"), N("y")), At(N("p"), N("b"), N("x"), N("y")))))))))))));

    private static Formula ClaimFormula()
    {
        var qcConditions = And(Call("QCStrategy", N("vac"), N("q"), N("p"), N("psi"), N("N")),
            And(Energy(Call("qcVacuum", N("vac"), N("q"), N("p"), N("psi"), N("x"))),
                Le(Call("taskValue", N("c"), Call("unitaryProb", N("Psi"), N("U"), N("M"))),
                    Call("taskValue", N("c"), Call("qcProb", N("q"), N("p"), N("psi"), N("N"))))));
        var unassisted = Some("H", N("Type"), SomeInstance(Call("NormedAddCommGroup", N("H")),
            SomeInstance(Call("InnerProductSpace", N("Complex"), N("H")),
                SomeInstance(Call("CompleteSpace", N("H")), Some("vac", N("H"),
                    Some("L", N("Type"), Some("K", N("Type"), Some("q", Weights(),
                        Some("p", EnsembleWeights(), Some("psi", Messages(),
                            Some("N", QCEffects(), qcConditions)))))))))));
        var comparison = Imp(Call("UnitaryStrategy", N("Psi"), N("U"), N("M")),
            Imp(Energy(Call("unitaryVacuum", N("Psi"), N("U"), N("x"))), unassisted));
        return IffFormula(N("claim"), Types(Instance(Call("Fintype", N("X")),
            Instance(Call("Fintype", N("Y")), Instance(Call("Fintype", N("B")),
                All("c", Behaviours(), All("omega", N("Real"), Imp(Le(D(0), N("omega")),
                    Imp(Lt(N("omega"), new Formula.Fraction(D(1), D(2))),
                        Dimensions(Instance(Call("NeZero", N("dA")), UnitaryData(comparison))))))))))));
    }
}
