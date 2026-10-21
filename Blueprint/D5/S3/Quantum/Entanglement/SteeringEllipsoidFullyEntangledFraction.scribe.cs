using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class SteeringEllipsoidFullyEntangledFractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.";
    private const string Owner = "D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction";
    private const string Geometry = "D5.S3.Quantum.Information.ActualPureQubitCostInfimum";
    private const string PartialTrace = "D5.S3.Quantum.Information.PartialTraceMutualInformation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/milne2014fullyentangledfraction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every two-qubit density matrix rho satisfies rho <= (2 - |c|)(1 tensor rho_B), where c is the centre of Alice's steering ellipsoid and rho_B is Bob's reduced state; hence its fully entangled fraction is at most 1 - |c|/2, and every value |c| = t in [0, 1] is attained by a state whose fully entangled fraction equals 1 - t/2. This proves Conjecture 2 of A. Milne, D. Jennings, S. Jevtic and T. Rudolph (arXiv:1404.3951).",
        H("The fully entangled fraction and the steering-ellipsoid centre"),
        Blocks(
            Node("pauli", "The Pauli matrices", PauliFormula(),
                "The three Pauli matrices sigma_x, sigma_y, sigma_z indexed by Fin 3. They are the Pauli matrices pauliMatrix of StabilizerPairLocalUnitaryInequivalence at the labels X, Y, Z: pauliMatrix X = qubitX = [[0, 1], [1, 0]], pauliMatrix Y = i qubitX qubitZ = [[0, -i], [i, 0]] and pauliMatrix Z = qubitZ = [[1, 0], [0, -1]]. Since Fin 3 has exactly the elements 0, 1, 2, the three displayed equations are the whole definition.",
                "pauli", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pauli-zero", "The first Pauli matrix", PauliZeroFormula(),
                "The Pauli matrix at index zero is the two-by-two matrix with zero diagonal entries and off-diagonal entries one.",
                "pauli_zero", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("pauli-one", "The second Pauli matrix", PauliOneFormula(),
                "The Pauli matrix at index one has zero diagonal entries, upper-right entry minus the imaginary unit and lower-left entry the imaginary unit.",
                "pauli_one", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("pauli-two", "The third Pauli matrix", PauliTwoFormula(),
                "The Pauli matrix at index two is diagonal with entries one and minus one.",
                "pauli_two", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("bloch-a", "Alice's Bloch vector", BlochAFormula(),
                "A two-qubit operator is a complex matrix indexed by pairs of qubit indices, the first entry of the pair belonging to Alice and the second to Bob. Following the companion paper, Theta_{mu nu} = tr(rho sigma_mu tensor sigma_nu): Alice's Bloch vector has components a_i = Re tr(rho (sigma_i tensor 1)), where kronecker is the Kronecker product and 1 the two-by-two identity.",
                "blochA", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bloch-b", "Bob's Bloch vector", BlochBFormula(),
                "Bob's Bloch vector has components b_j = Re tr(rho (1 tensor sigma_j)).",
                "blochB", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("corr", "The correlation matrix", CorrFormula(),
                "The correlation matrix has entries T_ij = Re tr(rho (sigma_i tensor sigma_j)), first index Alice.",
                "corr", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("vlen", "Euclidean length", VlenFormula(),
                "The Euclidean length of a real three-vector, the square root of the sum of the squares of its components. The scalar c of the conjecture is the length of the centre vector: the paper writes “For c = (0, 0, c)” and plots against “the magnitude of the steering ellipsoid centre”.",
                "vlen", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("centre", "The centre of the steering ellipsoid", CentreFormula(),
                "Section I of the paper: “Given all possible measurements by Bob, the set of Bloch vectors to which Alice can be steered forms her steering ellipsoid E inside the Bloch sphere. E is described by its centre c and a real, symmetric 3 x 3 matrix Q.” The companion paper of Jevtic, Pusey, Jennings and Rudolph (PRL 113, 020402) gives the centre: “This gives a steering ellipsoid centred at c_A = (a - T b)/(1 - b^2)”, and “If b = 1 then rho is a product state in which case there is no steering and the steering ellipsoid is the single point a.” The definition takes c = (a - T b)/(1 - |b|^2) when |b| is not 1 and c = a when |b| = 1; the display states it coordinate by coordinate, with (T b)_i the sum over j of T_ij b_j.",
                "centre", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("max-entangled", "Maximally entangled vectors", MaxEntangledFormula(),
                "A two-qubit vector e is maximally entangled when it is a unit vector and both of its reduced states are half the identity: partialTraceRight traces out Bob and partialTraceLeft traces out Alice from the rank-one operator vecMulVec e (star e) = |e><e|, and (1/2) 1 is the scalar multiple of the identity. For two qubits these are exactly the vectors (U tensor V)(|00> + |11>)/sqrt 2 with U, V unitary.",
                "IsMaxEntangled", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fef", "The fully entangled fraction", FefFormula(),
                "Section III of the paper: “The fully entangled fraction of a bipartite state rho is defined by f(rho) = max_phi <phi| rho |phi>, where the maximum is taken over all maximally entangled states |phi>.” The definition takes the supremum of the real expectation Re <e| rho |e> = re(star e . (rho e)) over all maximally entangled e; for a density matrix the set is non-empty and bounded, and attainment of the maximum is not used.",
                "fef", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 2", ClaimFormula(),
                "Section V, Conjecture 2: “Let rho be a general two-qubit state with E centred at c. The fully entangled fraction is tightly bounded as f(rho) <= 1 - c/2.” A two-qubit state is a positive semidefinite complex 4 x 4 matrix of trace 1. The first conjunct is the bound for every state; the second makes “tightly” precise: for every t in [0, 1] there is a state with |c| = t and fully entangled fraction exactly 1 - t/2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bloch-vec", "Bloch coordinates of a qubit operator", BlochVecFormula(),
                "For any complex two-by-two matrix X, the ith Bloch coordinate is the real part of the trace of X times the ith Pauli matrix. No Hermitian or trace condition is required in this definition.",
                "blochVec", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("ev", "The computational vector at zero and one", EvFormula(),
                "The real vector ev has value one at the pair (0, 1) and zero at the other three pairs of qubit labels.",
                "ev", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("vlen-eq-norm", "Euclidean length as a norm", VlenEqNormFormula(),
                "The length vlen of a real three-vector equals the norm of that vector in EuclideanSpace, with WithLp.toLp 2 identifying the coordinate function with its Euclidean vector.",
                "vlen_eq_norm", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("vlen-nonneg", "Euclidean length is nonnegative", VlenNonnegFormula(),
                "Every real three-vector has nonnegative Euclidean length, since its length is a real square root.",
                "vlen_nonneg", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("trace-mul-kron-one", "Tracing an Alice observable", TraceMulKronOneFormula(),
                "The trace of rho times A tensor the identity equals the trace of Alice's reduced operator times A. This identity holds for arbitrary complex operators, without positivity or normalization assumptions.",
                "trace_mul_kron_one", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("trace-mul-one-kron", "Tracing a Bob observable", TraceMulOneKronFormula(),
                "The trace of rho times the identity tensor B equals the trace of Bob's reduced operator times B. This identity holds for arbitrary complex operators, without positivity or normalization assumptions.",
                "trace_mul_one_kron", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("trace-conj-kron", "Moving a local filter across the trace", TraceConjKronFormula(),
                "For arbitrary complex two-by-two matrices K and A and a complex two-qubit operator rho, the trace of the operator filtered by the identity tensor K against A tensor the identity equals the trace of rho against A tensor K adjoint times K. This follows from cyclicity of the trace and multiplication of Kronecker products.",
                "trace_conj_kron", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("kron-sub", "The Kronecker product distributes over subtraction", KronSubFormula(),
                "For arbitrary complex two-by-two matrices A, X and Y, A tensor (X minus Y) equals A tensor X minus A tensor Y.",
                "kron_sub", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("vlen-e3", "Length on the third coordinate axis", VlenE3Formula(),
                "For every real s, the Euclidean length of (0, 0, s) is the absolute value of s.",
                "vlen_e3", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("bloch-vec-eq-bloch", "Agreement of Hermitian Bloch coordinates", BlochVecEqBlochFormula(),
                "For every Hermitian complex two-by-two matrix Z, the coordinates blochVec Z, regarded as a Euclidean vector, equal the Bloch vector bloch Z of ActualPureQubitCostInfimum.",
                "blochVec_eq_bloch", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("canonical-filter", "A canonical state and a reverse Bob filter", CanonicalFilterFormula(),
                "Let rho be positive semidefinite with trace one and Bob Bloch length strictly less than one. There are a positive semidefinite two-qubit operator sigma with Bob marginal half the identity and Alice Bloch vector equal to centre rho, and a complex two-by-two filter F which reconstructs rho from sigma. The filter satisfies F F adjoint = 2 rho_B, and the squared complex norm of its determinant is 1 minus the squared Bob Bloch length.",
                "canonical_filter", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("canonical-trace", "Normalization from the Bob marginal", CanonicalTraceFormula(),
                "Every complex two-qubit operator whose Bob marginal is half the identity has trace one. Positivity is not required for this trace identity.",
                "canonical_trace", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("canonical-bound", "States with a maximally mixed Bob marginal", CanonicalFormula(),
                "Let sigma be positive semidefinite with Bob marginal sigma_B = 1/2 (so its trace is 1), let a be the Bloch vector of its Alice marginal sigma_A, and let phi be a vector with t = <phi| sigma |phi> > 0. Put w = sigma phi. The Cauchy-Schwarz inequality for the positive form of sigma gives sigma >= w w^H / t and t^2 <= |phi|^2 |w|^2. For a two-by-two Hermitian X let rad X be the length of its Bloch vector, the difference of its eigenvalues; it is a seminorm, rad(sigma_A) = |a|, and rad Z <= tr Z for positive semidefinite Z because det Z >= 0. Taking Bob's marginal of sigma - w w^H / t gives 1/2 - tr_A(w w^H)/t >= 0, hence rad(tr_A w w^H)/t <= 1 - |w|^2/t. The two marginals of the rank-one operator w w^H have the same trace |w|^2 and the same determinant |det W|^2, W the coefficient matrix of w, so they have the same rad. Taking Alice's marginal, sigma_A = tr_B(w w^H)/t + Z with Z >= 0 and tr Z = 1 - |w|^2/t, so |a| <= rad(tr_B w w^H)/t + tr Z <= 2 - 2|w|^2/t <= 2 - 2t/|phi|^2. This is the bound; for t = 0 it follows from |a| <= 1.",
                "canonical_bound", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("operator-bound", "The operator inequality", OperatorFormula(),
                "Let rho be a two-qubit density matrix with Bob marginal rho_B = [[p, q], [conj q, r]] and Bloch vector b, so that 1 - |b|^2 = 4d with d = pr - |q|^2 = det rho_B. If |b| < 1 then d > 0 and p > 0; with u = sqrt d the filters H = [[u, 0], [-conj q, p]] and G = [[p, 0], [conj q, u]] satisfy H rho_B H^H = p d 1, G H = p u 1, G G^H = p rho_B and H^H H = p (1 - rho_B). The filtered operator sigma = (1 tensor H) rho (1 tensor H)^H / (2 p d) is positive semidefinite with Bob marginal 1/2, and since 2(1 - rho_B) = 1 - b . sigma its Alice Bloch vector is (a - T b)/(1 - |b|^2) = c. Moreover rho = (2/p)(1 tensor G) sigma (1 tensor G)^H, so for y = (1 tensor G)^H x the bound for sigma gives Re <x| rho |x> = (2/p) Re <y| sigma |y> <= (2/p)(1 - |c|/2) p <x| 1 tensor rho_B |x>. If |b| = 1 then c = a and |a| <= 1, and it suffices to show Re <x| rho |x> <= <x| 1 tensor rho_B |x>: with t = <x| rho |x> > 0 and w = rho x, the Cauchy-Schwarz bound rho >= w w^H / t gives rho_B >= tr_A(w w^H)/t, and rad(rho_B) = tr rho_B = 1 forces rad = tr for tr_A(w w^H), so det W = 0. Then A = W conj(X)^T is a rank-one two-by-two matrix with tr A = <x|w> = t, and |tr A|^2 <= sum |A_ik|^2 = tr(tr_A(w w^H) tr_A(x x^H)) <= t tr(rho_B tr_A(x x^H)) = t <x| 1 tensor rho_B |x>.",
                "operator_bound", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Proof of the conjecture", Disp(ClaimBody()),
                "For a maximally entangled e the reduced state tr_A(e e^H) is 1/2, so <e| 1 tensor rho_B |e> = tr(rho_B)/2 = 1/2, and the operator inequality gives Re <e| rho |e> <= (2 - |c|)/2 = 1 - |c|/2; the vector ((1 + i)/2)(|00> + |11>), a phase multiple of (|00> + |11>)/sqrt 2, is maximally entangled, so the supremum is at most 1 - |c|/2. For tightness let 0 <= t <= 1, chi = |00> + (1 - t)|11> and rho_t = (|chi><chi| + t(1 - t)|01><01|)/(2 - t), a density matrix. Its Bloch data are a = (0, 0, t(3 - 2t)/(2 - t)), b = (0, 0, t/(2 - t)), T_xz = T_yz = 0 and T_zz = (2 - 3t + 2t^2)/(2 - t). For t < 1 one has |b| < 1 and c = (a - T b)/(1 - |b|^2) = (0, 0, t); for t = 1 the state is |00><00|, |b| = 1 and c = a = (0, 0, 1). In both cases |c| = t, and the phase multiple of (|00> + |11>)/sqrt 2 gives Re <e| rho_t |e> = (1 + 2(1 - t) + (1 - t)^2)/(2(2 - t)) = 1 - t/2, which together with the bound fixes the supremum.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("milne-jennings-jevtic-rudolph-2014-fully-entangled-fraction"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("milne-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula AtMost(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(params Formula[] clauses)
    {
        Formula body = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--)
        {
            body = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And, Parenthesized(body));
        }
        return body;
    }
    private static Formula Half() => new Formula.Fraction(D(1), D(2));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Qubits() => Parenthesized(Seq(Fin(2), Sp, Times, Sp, Fin(2)));
    private static Formula Operators() => Call("Matrix", Qubits(), Qubits(), Complex());
    private static Formula Vectors() => Arrow(Qubits(), Complex());
    private static Formula RealVectors() => Arrow(Fin(3), Real());
    private static Formula Kron(Formula a, Formula b) => Call("kronecker", a, b);
    private static Formula RealPart(Formula value) => Call("re", value);
    private static Formula Tr(Formula value) => Call("trace", value);
    private static Formula Expect(Formula op, Formula x) =>
        RealPart(Call("dotProduct", Call("star", x), Call("mulVec", op, x)));
    private static Formula Length(Formula v) => Call("vlen", v);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(name), Colon, type)), Sp, Parenthesized(body));

    private static Formula Qualified(params string[] parts)
    {
        Formula result = Name(parts[0]);
        for (var i = 1; i < parts.Length; i++)
            result = Seq(result, Dot, Name(parts[i]));
        return result;
    }
    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Qualified([.. owner.Split('.'), name]), [.. arguments]);
    private static Formula QubitOperators() => Call("Matrix", Fin(2), Fin(2), Complex());
    private static Formula EuclideanVectors() => Call("EuclideanSpace", Real(), Fin(3));
    private static Formula Euclidean(Formula vector) =>
        Parenthesized(Seq(QCall("WithLp", "toLp", D(2), vector), Colon, Sp, EuclideanVectors()));
    private static Formula Adjoint(Formula matrix) => QCall("Matrix", "conjTranspose", matrix);
    private static Formula Scaled(Formula scalar, Formula matrix) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula Triple(Formula first, Formula second, Formula third) =>
        Seq(OpenBracket, first, Comma, Sp, second, Comma, Sp, third, CloseBracket);
    private static Formula QTr(Formula matrix) => QCall("Matrix", "trace", matrix);
    private static Formula QKron(Formula left, Formula right) => QCall("Matrix", "kronecker", left, right);
    private static Formula QLength(Formula vector) => QCall(Owner, "vlen", vector);
    private static Formula VlenNonnegFormula() => Disp(All("v", Arrow(Fin(3), Real()),
        AtMost(D(0), QLength(F.Id("v")))));
    private static Formula BobMarginal(Formula matrix) => QCall(PartialTrace, "partialTraceLeft", matrix);

    private static Formula BlochVecFormula()
    {
        Formula x = F.Id("X"), i = F.Id("i");
        return Disp(All("X", QubitOperators(), All("i", Fin(3),
            Equal(QCall(Owner, "blochVec", x, i),
                QCall("Complex", "re", QTr(Multiply(x, QCall(Owner, "pauli", i))))))));
    }

    private static Formula EvFormula()
    {
        Formula k = F.Id("k");
        Formula rowOne = Seq(OpenBracket, D(0), Comma, Sp, D(1), CloseBracket);
        Formula rowTwo = Seq(OpenBracket, D(0), Comma, Sp, D(0), CloseBracket);
        Formula entries = Seq(OpenBracket, rowOne, Comma, Sp, rowTwo, CloseBracket);
        return Disp(All("k", Qubits(), Equal(QCall(Owner, "ev", k),
            At(At(entries, QCall("Prod", "fst", k)), QCall("Prod", "snd", k)))));
    }

    private static Formula VlenEqNormFormula()
    {
        Formula v = F.Id("v");
        return Disp(All("v", RealVectors(), Equal(QLength(v), new Formula.Norm(Euclidean(v)))));
    }

    private static Formula TraceMulKronOneFormula()
    {
        Formula rho = F.Id("rho"), a = F.Id("A");
        return Disp(All("rho", Operators(), All("A", QubitOperators(),
            Equal(QTr(Multiply(rho, QKron(a, D(1)))),
                QTr(Multiply(QCall(PartialTrace, "partialTraceRight", rho), a))))));
    }

    private static Formula TraceMulOneKronFormula()
    {
        Formula rho = F.Id("rho"), b = F.Id("B");
        return Disp(All("rho", Operators(), All("B", QubitOperators(),
            Equal(QTr(Multiply(rho, QKron(D(1), b))), QTr(Multiply(BobMarginal(rho), b))))));
    }

    private static Formula TraceConjKronFormula()
    {
        Formula k = F.Id("K"), a = F.Id("A"), rho = F.Id("rho");
        Formula local = QKron(D(1), k);
        Formula filtered = Multiply(Multiply(Multiply(local, rho), Adjoint(local)), QKron(a, D(1)));
        return Disp(All("K", QubitOperators(), All("A", QubitOperators(), All("rho", Operators(),
            Equal(QTr(filtered), QTr(Multiply(rho, QKron(a, Multiply(Adjoint(k), k)))))))));
    }

    private static Formula KronSubFormula()
    {
        Formula a = F.Id("A"), x = F.Id("X"), y = F.Id("Y");
        return Disp(All("A", QubitOperators(), All("X", QubitOperators(), All("Y", QubitOperators(),
            Equal(QKron(a, Subtract(x, y)), Subtract(QKron(a, x), QKron(a, y)))))));
    }

    private static Formula VlenE3Formula()
    {
        Formula s = F.Id("s");
        return Disp(All("s", Real(), Equal(QLength(Triple(D(0), D(0), s)), new Formula.Absolute(s))));
    }

    private static Formula BlochVecEqBlochFormula()
    {
        Formula z = F.Id("Z");
        return Disp(All("Z", QubitOperators(), Implies(QCall("Matrix", "IsHermitian", z),
            Equal(Euclidean(QCall(Owner, "blochVec", z)), QCall(Geometry, "bloch", z)))));
    }

    private static Formula CanonicalFilterFormula()
    {
        Formula rho = F.Id("rho"), sigma = F.Id("sigma"), filter = F.Id("F");
        Formula bobLength = QLength(QCall(Owner, "blochB", rho));
        Formula localFilter = QKron(D(1), filter);
        Formula conclusions = And(
            QCall("Matrix", "PosSemidef", sigma),
            Equal(BobMarginal(sigma), Scaled(Half(), D(1))),
            Equal(QCall(Owner, "blochA", sigma), QCall(Owner, "centre", rho)),
            Equal(rho, Multiply(Multiply(localFilter, sigma), Adjoint(localFilter))),
            Equal(Multiply(filter, Adjoint(filter)), Scaled(D(2), BobMarginal(rho))),
            Equal(QCall("Complex", "normSq", QCall("Matrix", "det", filter)),
                Subtract(D(1), new Formula.Power(bobLength, D(2)))));
        Formula states = Some("sigma", Operators(), Some("F", QubitOperators(), conclusions));
        return Disp(All("rho", Operators(), Implies(QCall("Matrix", "PosSemidef", rho),
            Implies(Equal(QTr(rho), D(1)),
                Implies(Rel(bobLength, FormulaRelationOperator.LessThan, D(1)), states)))));
    }

    private static Formula CanonicalTraceFormula()
    {
        Formula sigma = F.Id("sigma");
        return Disp(All("sigma", Operators(),
            Implies(Equal(BobMarginal(sigma), Scaled(Half(), D(1))), Equal(QTr(sigma), D(1)))));
    }

    private static Formula MatrixTwo(Formula a, Formula b, Formula c, Formula d) =>
        Seq(Begin, Grp(F.Id("pmatrix")), a, Amp, b, RowBreak,
            c, Amp, d, End, Grp(F.Id("pmatrix")));

    private static Formula PauliZeroFormula() => Disp(Equal(
        QCall(Owner, "pauli", D(0)), MatrixTwo(D(0), D(1), D(1), D(0))));

    private static Formula PauliOneFormula() => Disp(Equal(
        QCall(Owner, "pauli", D(1)), MatrixTwo(D(0),
            Seq(Minus, Qualified("Complex", "I")), Qualified("Complex", "I"), D(0))));

    private static Formula PauliTwoFormula() => Disp(Equal(
        QCall(Owner, "pauli", D(2)), MatrixTwo(D(1), D(0), D(0), Seq(Minus, D(1)))));

    private static Formula PauliFormula() => Disp(And(
        Equal(Call("pauli", D(0)), Call("pauliMatrix", Name("X"))),
        Equal(Call("pauli", D(1)), Call("pauliMatrix", Name("Y"))),
        Equal(Call("pauli", D(2)), Call("pauliMatrix", Name("Z")))));

    private static Formula BlochAFormula()
    {
        Formula rho = F.Id("rho"), i = F.Id("i");
        return Disp(All("rho", Operators(), All("i", Fin(3), Equal(Call("blochA", rho, i),
            RealPart(Tr(Multiply(rho, Kron(Call("pauli", i), D(1)))))))));
    }

    private static Formula BlochBFormula()
    {
        Formula rho = F.Id("rho"), j = F.Id("j");
        return Disp(All("rho", Operators(), All("j", Fin(3), Equal(Call("blochB", rho, j),
            RealPart(Tr(Multiply(rho, Kron(D(1), Call("pauli", j)))))))));
    }

    private static Formula CorrFormula()
    {
        Formula rho = F.Id("rho"), i = F.Id("i"), j = F.Id("j");
        return Disp(All("rho", Operators(), All("i", Fin(3), All("j", Fin(3), Equal(Call("corr", rho, i, j),
            RealPart(Tr(Multiply(rho, Kron(Call("pauli", i), Call("pauli", j))))))))));
    }

    private static Formula VlenFormula()
    {
        Formula v = F.Id("v"), i = F.Id("i");
        return Disp(All("v", RealVectors(), Equal(Length(v),
            Seq(Sqrt, Grp(SumOver("i", Fin(3), new Formula.Power(At(v, i), D(2))))))));
    }

    private static Formula CentreFormula()
    {
        Formula rho = F.Id("rho"), i = F.Id("i"), j = F.Id("j");
        Formula b = Call("blochB", rho);
        Formula numerator = Subtract(Call("blochA", rho, i),
            SumOver("j", Fin(3), Multiply(Call("corr", rho, i, j), Call("blochB", rho, j))));
        Formula generic = new Formula.Fraction(numerator, Subtract(D(1), new Formula.Power(Length(b), D(2))));
        return Disp(All("rho", Operators(), All("i", Fin(3), Equal(At(Call("centre", rho), i),
            Call("ite", Equal(Length(b), D(1)), Call("blochA", rho, i), generic)))));
    }

    private static Formula MaxEntangledFormula()
    {
        Formula e = F.Id("e"), k = F.Id("k");
        Formula projector = Call("vecMulVec", e, Call("star", e));
        Formula unit = Equal(SumOver("k", Qubits(), new Formula.Power(new Formula.Norm(At(e, k)), D(2))), D(1));
        return Disp(All("e", Vectors(), Iff(Call("IsMaxEntangled", e), And(unit,
            Equal(Call("partialTraceRight", projector), Multiply(Half(), D(1))),
            Equal(Call("partialTraceLeft", projector), Multiply(Half(), D(1)))))));
    }

    private static Formula FefFormula()
    {
        Formula rho = F.Id("rho"), e = F.Id("e"), f = F.Id("f");
        Formula set = Seq(OpenBrace, f, Sp, Mid, Sp,
            Some("e", Vectors(), And(Call("IsMaxEntangled", e), Equal(f, Expect(rho, e)))), CloseBrace);
        return Disp(All("rho", Operators(), Equal(Call("fef", rho), Call("sSup", set))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), ClaimBody()));

    private static Formula ClaimBody()
    {
        Formula rho = F.Id("rho"), t = F.Id("t");
        Formula bound = All("rho", Operators(), Implies(Call("PosSemidef", rho), Implies(Equal(Tr(rho), D(1)),
            AtMost(Call("fef", rho), Subtract(D(1), new Formula.Fraction(Length(Call("centre", rho)), D(2)))))));
        Formula tight = All("t", Real(), Implies(AtMost(D(0), t), Implies(AtMost(t, D(1)), Some("rho", Operators(),
            And(Call("PosSemidef", rho), Equal(Tr(rho), D(1)), Equal(Length(Call("centre", rho)), t),
                Equal(Call("fef", rho), Subtract(D(1), new Formula.Fraction(t, D(2)))))))));
        return And(bound, tight);
    }

    private static Formula CanonicalFormula()
    {
        Formula sigma = F.Id("sigma"), phi = F.Id("phi");
        Formula factor = Parenthesized(Subtract(D(1), new Formula.Fraction(Length(Call("blochA", sigma)), D(2))));
        return Disp(All("sigma", Operators(), Implies(Call("PosSemidef", sigma),
            Implies(Equal(Call("partialTraceLeft", sigma), Multiply(Half(), D(1))),
                All("phi", Vectors(), AtMost(Expect(sigma, phi),
                    Multiply(factor, RealPart(Call("dotProduct", Call("star", phi), phi)))))))));
    }

    private static Formula OperatorFormula()
    {
        Formula rho = F.Id("rho"), x = F.Id("x");
        Formula factor = Parenthesized(Subtract(D(2), Length(Call("centre", rho))));
        return Disp(All("rho", Operators(), Implies(Call("PosSemidef", rho), Implies(Equal(Tr(rho), D(1)),
            All("x", Vectors(), AtMost(Expect(rho, x),
                Multiply(factor, Expect(Kron(D(1), Call("partialTraceLeft", rho)), x))))))));
    }
}
