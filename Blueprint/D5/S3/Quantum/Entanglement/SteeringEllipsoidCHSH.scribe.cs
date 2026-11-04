using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class SteeringEllipsoidCHSHDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH.";
    private const string Companion = "D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction";
    private const string SpinOwner = "D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/milne2014fullyentangledfraction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every two-qubit density matrix with steering-ellipsoid centre of length c has CHSH nonlocality at most max(2 sqrt(2(1 - c)), 2). At every c in [0, 1] this is the supremum over states with that centre length, proving Conjecture 1 of Milne, Jennings, Jevtic and Rudolph.",
        H("The steering-ellipsoid CHSH bound"),
        Blocks(
            Node("bell", "The CHSH operator", BellFormula(),
                "Section II defines B = alpha dot sigma tensor (beta + beta prime) dot sigma + alpha prime dot sigma tensor (beta - beta prime) dot sigma. The displayed variables aPrime and bPrime denote the primed directions. Matrix.kronecker is Mathlib's Kronecker product, the alias of Matrix.kroneckerMap with multiplication of complex entries. The four vectors here are arbitrary; unit lengths are required in the value set.",
                "bell", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("chsh-values", "CHSH expectation values", ChshValuesFormula(),
                "Section II maximizes the absolute value of tr(rho B) over four measurement directions. The set contains precisely these complex norms for unit directions, with Euclidean length D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.vlen. Its definition permits any two-qubit operator rho.",
                "chshValues", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("chsh", "CHSH nonlocality", ChshFormula(),
                "Section II: the maximal CHSH violation is beta(rho) = max_B |tr(rho B)|, where the maximization is over all four directions. The definition uses sSup of the real value set. This set is nonempty and bounded above for every two-qubit operator, and the proof uses no attainment assumption.",
                "chsh", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bound", "The centre bound", BoundFormula(),
                "Section V, Conjecture 1, gives the maximum of 2 sqrt(2(1 - t)) and 2. The function is defined for every real t with Mathlib's Real.sqrt; the tightness statement restricts t to [0, 1].",
                "bound", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "Section V, Conjecture 1: Let rho be a general two-qubit state with its steering ellipsoid centred at c. The CHSH nonlocality is tightly bounded as beta(rho) <= max[2 sqrt(2(1 - c)), 2]. Here c is the Euclidean length of D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.centre. The first clause gives the inequality for every positive semidefinite matrix of trace one. The second expresses tightness as a supremum: for each t in [0, 1] and each epsilon > 0 there is a positive semidefinite trace-one matrix with centre length exactly t and CHSH value strictly greater than bound(t) - epsilon.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sigma-succ", "Agreement of Pauli indexing", SigmaSuccFormula(),
                "For every index i in Fin 3, the Pauli operator sigma at the successor index in Fin 4 equals pauli i.",
                "sigma_succ", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("vlen-sq", "Squared Euclidean length", VlenSqFormula(),
                "For every real three-vector, the square of its Euclidean length equals its dot product with itself.",
                "vlen_sq", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("normalized-unit", "Unit normalization", NormalizedUnitFormula(),
                "Every nonzero real three-vector becomes unit length after division by its Euclidean length, and rescaling the normalized vector recovers the original vector.",
                "normalized_unit", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("trace-pauli-kronecker-eq-corr", "Pauli expectations equal the correlations", TracePauliKroneckerEqCorrFormula(),
                "For every Hermitian complex two-qubit operator rho and every pair of Pauli indices i and j in Fin 3, the trace of rho times the corresponding Kronecker product equals its real correlation entry embedded in the complex numbers. Hermiticity makes this trace real.",
                "trace_pauli_kronecker_eq_corr", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("delta", "The difference of global and marginal purities", DeltaFormula(),
                "Delta(X) is the real trace of X squared minus the real trace of its Alice marginal squared. The partial trace is over Bob's factor. This real-valued definition applies to every complex two-qubit matrix X.",
                "delta", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("flip-matrix", "A direction-dependent spin flip", FlipMatrixFormula(),
                "For a real three-vector n, the conjugating matrix is the tensor product of the second Pauli matrix with spin(n) times that Pauli matrix. No unit-length condition is imposed in this definition.",
                "flipMatrix", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("flipped", "The flipped matrix", FlippedFormula(),
                "Transpose X in the product basis and multiply it on the left by flipMatrix(n) and on the right by its adjoint. This construction preserves positive semidefiniteness because transposition and conjugation preserve it.",
                "flipped", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("flip-purity-identity", "The directional flip identity", FlipPurityIdentityFormula(),
                "For a Hermitian trace-one matrix and a unit direction n, the real trace pairing with the flipped matrix, the squared Frobenius sum of the correlations, the squared length of Tn and Bob's squared component along n satisfy this identity. Expanding the Pauli matrices gives its homogeneous form; trace one and the unit length of n give the displayed normalization.",
                "flip_purity_identity", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("unit-dot-le", "A unit direction bounds a component", UnitDotLeFormula(),
                "The absolute component of a real three-vector x along a unit vector a is at most the Euclidean length of x. This is the real inner-product Cauchy-Schwarz inequality.",
                "unit_dot_le", DescribeRole.Lemma,
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/axler2024innerproduct"))),
            Node("bob-radius-le", "Bob's Bloch vector lies in the unit ball", BobRadiusLeFormula(),
                "A positive semidefinite trace-one two-qubit matrix has a positive semidefinite trace-one Bob marginal. The norm of that marginal's Bloch vector is at most its trace, hence at most one.",
                "bob_radius_le", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("delta-le-centre", "Purity difference bounded by the ellipsoid centre", DeltaLeCentreFormula(),
                "The purity difference is at most (1 - |b| squared)(1/2 - |centre(rho)|). When |b| < 1 an invertible filter makes Bob's marginal maximally mixed; determinant scaling of Delta and the canonical state's eigenvalue bound give the inequality. When |b| = 1, support on Bob's pure marginal makes Delta zero, giving the boundary case.",
                "delta_le_centre", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("bell-trace-real-expansion", "The real correlation form of a CHSH expectation", BellTraceRealExpansionFormula(),
                "For a Hermitian two-qubit matrix, the CHSH expectation equals the sum of the two real correlation dot products embedded in the complex numbers. Expanding the two Pauli observables and using real Pauli expectations gives the equality for arbitrary directions.",
                "bell_trace_real_expansion", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("tight-vector", "The vector supported on the two equal-bit basis states", TightVectorFormula(),
                "The vector has amplitudes sqrt(1+s) at (0,0), sqrt((1-t)(1-s)) at (1,1), and zero at the other two product indices. The real amplitudes are explicitly embedded in the complex numbers. The definition permits arbitrary real t and s.",
                "tightVector", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tight-state", "A two-term family of matrices", TightStateFormula(),
                "Take half the outer product of tightVector with its adjoint and add t(1-s)/2 times the projector onto the product basis vector (0,1). The latter vector is the real vector ev embedded coordinatewise in the complex numbers. The formula defines the family for all real parameters.",
                "tightState", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tight-psd", "Positivity of the two-term family", TightPsdFormula(),
                "If t is nonnegative and s is at most one, both coefficients in tightState are nonnegative. Each outer product is positive semidefinite, so their sum is positive semidefinite.",
                "tight_psd", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("tight-readouts", "Trace, Bloch vectors and correlations of the family", TightReadoutsFormula(),
                "For t <= 1 and 0 <= s <= 1, the matrix has trace one, both Bloch vectors lie on the third axis, and its correlation matrix is diagonal. The first two diagonal entries are opposite and equal in magnitude to sqrt(1+s) sqrt((1-t)(1-s)); the third is 1-t+ts. These equalities follow by evaluating the four product-basis entries and the Pauli traces.",
                "tight_readouts", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("tight-centre", "The centre length of the family", TightCentreFormula(),
                "For 0 <= t <= 1 and 0 <= s < 1, Bob's Bloch length is s, so the centre denominator, one minus s squared, is nonzero. Substituting the Bloch vectors and diagonal correlations gives Alice's centre (0,0,t), whose length is t.",
                "tight_centre", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("milne-chsh-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The centre bound holds"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Write T for the correlation matrix, b for Bob's Bloch vector and Delta(X) = Re tr(X squared) - Re tr((tr_B X) squared). For orthonormal u, v and their normal n, conjugate the full transpose of rho by sigma_y tensor ((n dot sigma) sigma_y). The sum |Tu| squared + |Tv| squared plus (b dot n) squared plus twice the real trace of rho times this flipped state equals 1 + 2 Delta(rho). The flipped state is positive semidefinite, so the plane sum is at most 1 + 2 Delta(rho). The sum and difference of Bob's two unit measurement directions are orthogonal; decomposing them and applying Cauchy-Schwarz reduces each CHSH expectation to twice the square root of such a plane sum.")),
                    Paragraph(Text(
                    "The two-by-two determinant polarization identity gives Delta((I tensor F)X(I tensor F) adjoint) = |det F| squared Delta(X). For a state sigma with Bob marginal I/2 and Alice Bloch length c, the canonical bound sigma <= (1 - c/2)I bounds its eigenvalues and yields Delta(sigma) <= 1/2 - c. An explicit invertible filter makes Bob's marginal maximally mixed when |b| < 1, giving Delta(rho) <= (1 - |b| squared)(1/2 - c). When |b| = 1, Bob's marginal is a projector; filtering by this projector leaves rho fixed and has determinant zero, so Delta(rho) = 0. Thus every plane sum is at most max(2(1 - c), 1), giving the stated CHSH bound.")),
                    Paragraph(Text(
                    "For tightness, let R(t, s) = |v><v|/2 + t(1 - s)|01><01|/2, where v = sqrt(1 + s)|00> + sqrt((1 - t)(1 - s))|11>. For 0 <= t <= 1 and 0 <= s < 1 this is a density matrix with centre (0, 0, t). At s = 0, CHSH settings in the xy plane attain 2 sqrt(2(1 - t)), proving tightness when t <= 1/2. For 1/2 < t < 1, the four z directions give 2(1 - t + ts); choosing s = 2/(2 + epsilon) makes this strictly greater than 2 - epsilon. At t = s = 1 the product state |00><00| has centre length one and CHSH value two."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("milne-jennings-jevtic-rudolph-2014-chsh-centre-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("milne-chsh-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Qualified(params string[] parts)
    {
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        for (var i = 1; i < parts.Length; i++)
            result = Seq(result, Dot, Operatorname, Grp(F.Id(parts[i])));
        return result;
    }

    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Qualified([.. owner.Split('.'), name]), [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula body = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            body = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And,
                Parenthesized(body));
        return body;
    }

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Pair(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Direction() => Arrow(Fin(3), Real());
    private static Formula MatrixType(Formula rows, Formula columns) =>
        Call("Matrix", rows, columns, Complex());
    private static Formula TwoQubitType() => MatrixType(Pair(Fin(2), Fin(2)), Pair(Fin(2), Fin(2)));

    private static Formula Vlen(Formula vector) => QCall(Companion, "vlen", vector);
    private static Formula Centre(Formula rho) => QCall(Companion, "centre", rho);
    private static Formula Trace(Formula matrix) => QCall("Matrix", "trace", matrix);
    private static Formula Positive(Formula matrix) => QCall("Matrix", "PosSemidef", matrix);
    private static Formula Kron(Formula left, Formula right) => QCall("Matrix", "kronecker", left, right);
    private static Formula Spin(Formula vector) => QCall(SpinOwner, "spin", vector);
    private static Formula Bell(Formula a, Formula aPrime, Formula b, Formula bPrime) =>
        Call("bell", a, aPrime, b, bPrime);
    private static Formula SigmaSuccFormula()
    {
        Formula i = F.Id("i");
        return All("i", Fin(3), EqTo(
            QCall(SpinOwner, "sigma", QCall("Fin", "succ", i)),
            QCall(Companion, "pauli", i)));
    }

    private static Formula VlenSqFormula()
    {
        Formula u = F.Id("u");
        return All("u", Direction(), EqTo(
            new Formula.Power(Parenthesized(Vlen(u)), D(2)),
            Call("dotProduct", u, u)));
    }

    private static Formula NormalizedUnitFormula()
    {
        Formula u = F.Id("u");
        Formula normalized = Seq(Parenthesized(Call("inv", Vlen(u))), Sp, Cdot, Sp,
            Parenthesized(u));
        Formula recovered = Seq(Parenthesized(Vlen(u)), Sp, Cdot, Sp,
            Parenthesized(normalized));
        return All("u", Direction(), Implies(
            Rel(u, FormulaRelationOperator.NotEqual, D(0)),
            And(
                EqTo(Vlen(normalized), D(1)),
                EqTo(recovered, u))));
    }

    private static Formula TracePauliKroneckerEqCorrFormula()
    {
        Formula rho = F.Id("rho"), i = F.Id("i"), j = F.Id("j");
        Formula observable = Kron(QCall(Companion, "pauli", i), QCall(Companion, "pauli", j));
        Formula correlation = QCall("Complex", "ofReal", QCall(Companion, "corr", rho, i, j));
        return All("rho", TwoQubitType(), Implies(QCall("Matrix", "IsHermitian", rho),
            All("i", Fin(3), All("j", Fin(3), EqTo(Trace(Multiply(rho, observable)), correlation)))));
    }

    private static Formula BellFormula()
    {
        var a = F.Id("a");
        var aPrime = F.Id("aPrime");
        var b = F.Id("b");
        var bPrime = F.Id("bPrime");
        var expression = Add(Kron(Spin(a), Spin(Add(b, bPrime))),
            Kron(Spin(aPrime), Spin(Subtract(b, bPrime))));
        return All("a", Direction(), All("aPrime", Direction(), All("b", Direction(),
            All("bPrime", Direction(), EqTo(Bell(a, aPrime, b, bPrime), expression)))));
    }

    private static Formula ChshValuesFormula()
    {
        var rho = F.Id("rho");
        var r = F.Id("r");
        var a = F.Id("a");
        var aPrime = F.Id("aPrime");
        var b = F.Id("b");
        var bPrime = F.Id("bPrime");
        var value = new Formula.Norm(Trace(Multiply(rho, Bell(a, aPrime, b, bPrime))));
        var conditions = And(
            EqTo(Vlen(a), D(1)), EqTo(Vlen(aPrime), D(1)), EqTo(Vlen(b), D(1)),
            EqTo(Vlen(bPrime), D(1)), EqTo(r, value));
        var predicate = Some("a", Direction(), Some("aPrime", Direction(), Some("b", Direction(),
            Some("bPrime", Direction(), conditions))));
        var set = Seq(OpenBrace, r, Sp, Colon, Sp, Real(), Sp, Mid, Sp, predicate, CloseBrace);
        return All("rho", TwoQubitType(), EqTo(Call("chshValues", rho), set));
    }

    private static Formula ChshFormula() =>
        All("rho", TwoQubitType(), EqTo(Call("chsh", F.Id("rho")),
            Call("sSup", Call("chshValues", F.Id("rho")))));

    private static Formula BoundFormula()
    {
        var t = F.Id("t");
        var squareRoot = QCall("Real", "sqrt", Multiply(D(2), Subtract(D(1), t)));
        return All("t", Real(), EqTo(Call("bound", t),
            Call("max", Multiply(D(2), squareRoot), D(2))));
    }

    private static Formula ClaimFormula() => Iff(F.Id("claim"), ClaimBody());

    private static Formula ClaimBody()
    {
        var rho = F.Id("rho");
        var t = F.Id("t");
        var epsilon = F.Id("epsilon");
        var centreLength = Vlen(Centre(rho));
        var universal = All("rho", TwoQubitType(),
            Implies(Positive(rho), Implies(EqTo(Trace(rho), D(1)),
                LessThanOrEqual(Call("chsh", rho), Call("bound", centreLength)))));
        var state = Some("rho", TwoQubitType(), And(
            Positive(rho), EqTo(Trace(rho), D(1)), EqTo(Vlen(Centre(rho)), t),
            LessThan(Subtract(Call("bound", t), epsilon), Call("chsh", rho))));
        var approximation = All("epsilon", Real(), Implies(LessThan(D(0), epsilon), state));
        var tight = All("t", Real(), Implies(LessThanOrEqual(D(0), t),
            Implies(LessThanOrEqual(t, D(1)), approximation)));
        return And(universal, tight);
    }

    private static Formula ExactSymbol(string name) => name switch
    {
        "ρ" => Rho,
        "a'" => Seq(F.Id("a"), Apos),
        "b'" => Seq(F.Id("b"), Apos),
        _ => F.Id(name),
    };
    private static Formula ExactTyped(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula ExactAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, ExactTyped(ExactSymbol(name), type), Comma, Sp, Parenthesized(body));
    private static Formula ExactLambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, ExactTyped(ExactSymbol(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula ExactSum(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, ExactTyped(ExactSymbol(name), Fin(3))), Sp, Parenthesized(body));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula RealPart(Formula value) => QCall("Complex", "re", value);
    private static Formula BlochA(Formula value) => QCall(Companion, "blochA", value);
    private static Formula BlochB(Formula value) => QCall(Companion, "blochB", value);
    private static Formula Corr(params Formula[] arguments) => QCall(Companion, "corr", arguments);
    private static Formula DotProduct(Formula left, Formula right) => Call("dotProduct", left, right);
    private static Formula MulVec(Formula matrix, Formula vector) => QCall("Matrix", "mulVec", matrix, vector);
    private static Formula SqrtOf(Formula value) => QCall("Real", "sqrt", value);
    private static Formula ComplexOfReal(Formula value) => QCall("Complex", "ofReal", value);
    private static Formula Hermitian(Formula value) => QCall("Matrix", "IsHermitian", value);
    private static Formula DensityHypotheses(Formula rho, Formula body) =>
        Implies(Positive(rho), Implies(EqTo(Trace(rho), ExactTyped(D(1), Complex())), body));
    private static Formula VectorLiteral(params Formula[] entries)
    {
        Formula body = entries[0];
        for (var i = 1; i < entries.Length; i++) body = Seq(body, Comma, Sp, entries[i]);
        return Seq(Bang, OpenBracket, body, CloseBracket);
    }
    private static Formula TightBinders(Formula body) => ExactAll("t", Real(), ExactAll("s", Real(), body));

    private static Formula DeltaFormula()
    {
        Formula x = ExactSymbol("X");
        Formula marginal = QCall("D5.S3.Quantum.Information.PartialTraceMutualInformation", "partialTraceRight", x);
        return ExactAll("X", TwoQubitType(), EqTo(Call("delta", x),
            Subtract(RealPart(Trace(Multiply(x, x))), RealPart(Trace(Multiply(marginal, marginal))))));
    }

    private static Formula FlipMatrixFormula()
    {
        Formula n = ExactSymbol("n");
        Formula pauli = QCall(Companion, "pauli", ExactTyped(D(1), Fin(3)));
        return ExactAll("n", Direction(), EqTo(Call("flipMatrix", n), Kron(pauli, Multiply(Spin(n), pauli))));
    }

    private static Formula FlippedFormula()
    {
        Formula x = ExactSymbol("X"), n = ExactSymbol("n"), matrix = Call("flipMatrix", n);
        return ExactAll("X", TwoQubitType(), ExactAll("n", Direction(), EqTo(Call("flipped", x, n),
            Multiply(Multiply(matrix, QCall("Matrix", "transpose", x)), QCall("Matrix", "conjTranspose", matrix)))));
    }

    private static Formula FlipPurityIdentityFormula()
    {
        Formula rho = Rho, n = ExactSymbol("n");
        Formula energy = ExactSum("i", ExactSum("j", Square(Corr(rho, ExactSymbol("i"), ExactSymbol("j")))));
        Formula left = Add(Subtract(Add(Multiply(D(2), RealPart(Trace(Multiply(rho, Call("flipped", rho, n))))),
            energy), Square(Vlen(MulVec(Corr(rho), n)))), Square(DotProduct(BlochB(rho), n)));
        return ExactAll("ρ", TwoQubitType(), Implies(Hermitian(rho),
            Implies(EqTo(Trace(rho), ExactTyped(D(1), Complex())), ExactAll("n", Direction(),
                Implies(EqTo(Vlen(n), D(1)), EqTo(left, Add(D(1), Multiply(D(2), Call("delta", rho)))))))));
    }

    private static Formula UnitDotLeFormula() => ExactAll("a", Direction(), ExactAll("x", Direction(),
        Implies(EqTo(Vlen(ExactSymbol("a")), D(1)), LessThanOrEqual(
            new Formula.Absolute(DotProduct(ExactSymbol("a"), ExactSymbol("x"))), Vlen(ExactSymbol("x"))))));

    private static Formula BobRadiusLeFormula() => ExactAll("ρ", TwoQubitType(),
        DensityHypotheses(Rho, LessThanOrEqual(Vlen(BlochB(Rho)), D(1))));

    private static Formula DeltaLeCentreFormula() => ExactAll("ρ", TwoQubitType(), DensityHypotheses(Rho,
        LessThanOrEqual(Call("delta", Rho), Multiply(Subtract(D(1), Square(Vlen(BlochB(Rho)))),
            Subtract(new Formula.Fraction(D(1), D(2)), Vlen(Centre(Rho)))))));

    private static Formula BellTraceRealExpansionFormula()
    {
        Formula a = ExactSymbol("a"), aPrime = ExactSymbol("a'"), b = ExactSymbol("b"), bPrime = ExactSymbol("b'");
        Formula realValue = Add(DotProduct(a, MulVec(Corr(Rho), Add(b, bPrime))),
            DotProduct(aPrime, MulVec(Corr(Rho), Subtract(b, bPrime))));
        return ExactAll("ρ", TwoQubitType(), Implies(Hermitian(Rho), ExactAll("a", Direction(),
            ExactAll("a'", Direction(), ExactAll("b", Direction(), ExactAll("b'", Direction(),
                EqTo(Trace(Multiply(Rho, Bell(a, aPrime, b, bPrime))), ComplexOfReal(realValue))))))));
    }

    private static Formula TightVectorFormula()
    {
        Formula t = ExactSymbol("t"), s = ExactSymbol("s"), k = ExactSymbol("k");
        Formula entries = VectorLiteral(VectorLiteral(ComplexOfReal(SqrtOf(Add(D(1), s))), ExactTyped(D(0), Complex())),
            VectorLiteral(ExactTyped(D(0), Complex()), ComplexOfReal(SqrtOf(Multiply(Subtract(D(1), t), Subtract(D(1), s))))));
        Formula first = QCall("Prod", "fst", k), second = QCall("Prod", "snd", k);
        Formula body = ExactLambda("k", Pair(Fin(2), Fin(2)), At(entries, first, second));
        return TightBinders(EqTo(Call("tightVector", t, s), body));
    }

    private static Formula TightStateFormula()
    {
        Formula t = ExactSymbol("t"), s = ExactSymbol("s");
        Formula vector = Call("tightVector", t, s);
        Formula ev = ExactLambda("k", Pair(Fin(2), Fin(2)), ComplexOfReal(QCall(Companion, "ev", ExactSymbol("k"))));
        Formula rankOne = QCall("Matrix", "vecMulVec", vector, QCall("Star", "star", vector));
        Formula evProjector = QCall("Matrix", "vecMulVec", ev, QCall("Star", "star", ev));
        Formula half = ExactTyped(new Formula.Fraction(D(1), D(2)), Complex());
        Formula coefficient = ComplexOfReal(new Formula.Fraction(Multiply(t, Subtract(D(1), s)), D(2)));
        Formula first = QCall("HSMul", "hSMul", half, rankOne);
        Formula second = QCall("HSMul", "hSMul", coefficient, evProjector);
        return TightBinders(EqTo(Call("tightState", t, s), Add(first, second)));
    }

    private static Formula TightPsdFormula() => TightBinders(Implies(LessThanOrEqual(D(0), ExactSymbol("t")),
        Implies(LessThanOrEqual(ExactSymbol("s"), D(1)), Positive(Call("tightState", ExactSymbol("t"), ExactSymbol("s"))))));

    private static Formula TightReadoutsFormula()
    {
        Formula t = ExactSymbol("t"), s = ExactSymbol("s"), state = Call("tightState", t, s);
        Formula p = Multiply(SqrtOf(Add(D(1), s)), SqrtOf(Multiply(Subtract(D(1), t), Subtract(D(1), s))));
        Formula readouts = And(EqTo(Trace(state), ExactTyped(D(1), Complex())),
            EqTo(BlochA(state), VectorLiteral(D(0), D(0), Add(t, Multiply(Subtract(D(1), t), s)))),
            EqTo(BlochB(state), VectorLiteral(D(0), D(0), s)),
            EqTo(Corr(state), QCall("Matrix", "diagonal", VectorLiteral(p, new Formula.Negate(Parenthesized(p)),
                Add(Subtract(D(1), t), Multiply(t, s))))));
        return TightBinders(Implies(LessThanOrEqual(t, D(1)), Implies(LessThanOrEqual(D(0), s),
            Implies(LessThanOrEqual(s, D(1)), readouts))));
    }

    private static Formula TightCentreFormula()
    {
        Formula t = ExactSymbol("t"), s = ExactSymbol("s");
        return TightBinders(Implies(LessThanOrEqual(D(0), t), Implies(LessThanOrEqual(t, D(1)),
            Implies(LessThanOrEqual(D(0), s), Implies(LessThan(s, D(1)),
                EqTo(Vlen(Centre(Call("tightState", t, s))), t))))));
    }
}
