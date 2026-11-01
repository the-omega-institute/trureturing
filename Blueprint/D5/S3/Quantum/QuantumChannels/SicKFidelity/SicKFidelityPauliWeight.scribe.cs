using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.SicKFidelity;

internal sealed class SicKFidelityPauliWeightDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mayer2021zerofidelity");
    private static readonly LibraryNoteRef SicSource =
        LibraryNoteRef.Create("D5/L/QuantumStates/renes2004sic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multi-qubit Pauli process matrices, Pauli-twirl weight distributions, single-qubit SIC projectors and overlap-inverse kernels, per-qubit diagonal functionals, the alternating binomial Pauli-weight formula for every SIC k-fidelity of an arbitrary linear qubit map, and alternating truncation bounds for completely positive maps.",
        H("Pauli-weight expansion and alternating truncation bounds for qubit SIC k-fidelities"),
        Blocks(
            Node("sickfidelity-qubit-index-definition", "Computational basis index", "QubitIndex",
                QubitIndexFormula(),
                "For n qubits, QubitIndex(n) is the function type Fin n -> Fin 2 indexing the 2^n computational basis vectors.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-pauli-label-definition", "Multi-qubit Pauli string label", "PauliLabel",
                PauliLabelFormula(),
                "For n qubits, PauliLabel(n) is the function type Fin n -> Fin 4 indexing the 4^n tensor-product Pauli strings.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-qubit-map-definition", "Linear superoperator on n qubits", "QubitMap",
                QubitMapFormula(),
                "For n qubits, QubitMap(n) is the space of complex-linear maps on 2^n by 2^n complex matrices.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-pauli1-definition", "Single-qubit Pauli matrices", "pauli1",
                Pauli1Formula(),
                "Maps 0, 1, 2, 3 in Fin 4 to the 2 by 2 complex matrices I, X, Y, Z.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-paulin-definition", "Tensor-product Pauli operator", "pauliN",
                PauliNFormula(),
                "For a multi-qubit label beta in PauliLabel(n), pauliN(n, beta) is the n-fold tensor-product matrix whose (x, y) entry is the product over i in Fin n of pauli1(beta(i))(x(i), y(i)).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-hamming-weight-definition", "Pauli Hamming weight", "hammingWeight",
                HammingWeightFormula(),
                "Counts the number of qubit positions i in Fin n at which beta(i) is nonzero.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-process-matrix-definition", "Pauli process-matrix coefficients", "processMatrix",
                ProcessMatrixFormula(),
                "Gives the unique expansion coefficient chi_{beta, gamma} of an n-qubit linear map Lambda in the basis X |-> P_beta X P_gamma by Hilbert-Schmidt contraction scaled by 4^{-n}.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-pauli-twirl-weight-definition", "Diagonal Pauli-twirl weight", "pauliTwirlWeight",
                PauliTwirlWeightFormula(),
                "Evaluates the diagonal Pauli process-matrix coefficient q_beta = chi_{beta, beta} of Lambda.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-pauli-weight-sum-definition", "Aggregated weight-w Pauli-twirl mass", "pauliWeightSum",
                PauliWeightSumFormula(),
                "Sums the diagonal Pauli-twirl weights q_beta(Lambda) over all labels beta of Hamming weight w.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-max-entangled-vec-definition", "Normalized maximally entangled state vector", "maxEntangledVec",
                MaxEntangledVecFormula(),
                "Defines the bipartite unit vector |Phi> = 2^{-n/2} sum_x |x> tensor |x> on QubitIndex(n) times QubitIndex(n).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sickfidelity-max-entangled-proj-definition", "Maximally entangled rank-one projector", "maxEntangledProj",
                MaxEntangledProjFormula(),
                "Forms the rank-one projector |Phi><Phi| = vecMulVec(|Phi>, star |Phi|) of the maximally entangled state.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sickfidelity-process-fidelity-definition", "Entanglement process fidelity", "processFidelity",
                ProcessFidelityFormula(),
                "Evaluates F(Lambda) = <Phi | (id tensor Lambda)(|Phi><Phi|) | Phi> relative to the identity superoperator.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sickfidelity-pauli-channel-definition", "Multi-qubit Pauli channel", "pauliChannel",
                PauliChannelFormula(),
                "Constructs the linear map X |-> sum_beta q_beta P_beta X P_beta associated with real weights q : PauliLabel(n) -> R.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-complex-pauli-twirl-definition", "Complex Pauli-twirled superoperator", "complexPauliTwirl",
                ComplexPauliTwirlFormula(),
                "Constructs the diagonal Pauli map X |-> sum_beta q_beta(Lambda) P_beta X P_beta sharing the Pauli-twirl weights of an arbitrary linear map Lambda.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-real-twirl-weight-definition", "Real part of a Pauli-twirl weight", "realTwirlWeight",
                RealTwirlWeightFormula(),
                "Projects pauliTwirlWeight(Lambda, beta) to its real part.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-real-weight-sum-definition", "Real part of the weight-w Pauli-twirl sum", "realWeightSum",
                RealWeightSumFormula(),
                "Projects pauliWeightSum(Lambda, w) to its real part.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-real-process-fidelity-definition", "Real part of entanglement process fidelity", "realProcessFidelity",
                RealProcessFidelityFormula(),
                "Projects processFidelity(Lambda) to its real part.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-is-qubit-sic-projector-definition", "Single-qubit SIC projector family", "IsQubitSICProjector",
                IsQubitSicProjectorFormula(),
                "Predicates that four 2 by 2 complex matrices are Hermitian, idempotent, unit-trace projectors with pairwise Hilbert-Schmidt inner product 1 / 3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(SicSource)),
            Node("sickfidelity-is-unit-vector-qubit-sic-definition", "Single-qubit unit-vector SIC family", "IsUnitVectorQubitSIC",
                IsUnitVectorQubitSicFormula(),
                "Predicates that four vectors in C^2 have unit norm and pairwise squared inner-product modulus 1 / 3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(SicSource)),
            Node("sickfidelity-sic-overlap-b-definition", "Single-qubit SIC overlap matrix B", "sicOverlapB",
                SicOverlapBFormula(),
                "Defines the 4 by 4 overlap matrix B = (2 / 3) I_4 + (1 / 3) J_4 with 1 on the diagonal and 1 / 3 off the diagonal.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(SicSource)),
            Node("sickfidelity-sic-matrix-a-definition", "Single-qubit overlap-inverse deviation matrix A", "sicMatrixA",
                SicMatrixAFormula(),
                "Defines A = (1 / 4) J_4 - (1 / 2) I_4 with -1 / 4 on the diagonal and 1 / 4 off the diagonal, satisfying B(I_4 - A) = I_4.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-product-sic-definition", "Tensor-product multi-qubit SIC projector", "productSIC",
                ProductSicFormula(),
                "Forms the n-qubit tensor-product projector rho^{(1)}_{a_1} tensor ... tensor rho^{(n)}_{a_n} from per-qubit SIC families.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sickfidelity-sic-subset-kernel-definition", "Subset tensor kernel M_T", "sicSubsetKernel",
                SicSubsetKernelFormula(),
                "Evaluates the entry (M_T)_{a, b} of the n-fold tensor product placing A on qubit positions in T and I_4 on positions outside T.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-kfidelity-definition", "Truncated SIC k-fidelity", "kFidelity",
                KFidelityFormula(),
                "Defines F_k(Lambda) = 4^{-n} sum_{|T| <= k} (-1)^{|T|} sum_{a, b} (M_T)_{a, b} Tr(rho_b Lambda(rho_a)) by truncating the overlap-inverse subset expansion to at most k factors of A.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-real-kfidelity-definition", "Real part of the SIC k-fidelity", "realKFidelity",
                RealKFidelityFormula(),
                "Projects kFidelity(rho, k, Lambda) to its real part.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-sic-e-definition", "Per-qubit diagonal SIC functional e", "sicE",
                SicEFormula(),
                "Defines e(beta, gamma) = (1 / 4) sum_a Tr(rho_a P_beta rho_a P_gamma) for a single-qubit family rho and Pauli indices beta, gamma.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(SicSource)),
            Node("sickfidelity-sic-alpha-definition", "Per-qubit A-weighted SIC functional alpha", "sicAlpha",
                SicAlphaFormula(),
                "Defines alpha(beta, gamma) = (1 / 4) sum_{a, b} A_{a, b} Tr(rho_b P_beta rho_a P_gamma) for a single-qubit family rho and Pauli indices beta, gamma.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(SicSource)),
            Node("sickfidelity-pauli-process-characterization-theorem",
                "Pauli process-matrix expansion, process fidelity identity, and CP/TP properties",
                "pauli_process_matrix_and_fidelity_characterization",
                PauliProcessCharacterizationFormula(),
                "Every n-qubit linear map Lambda admits a unique expansion Lambda(X) = sum_{beta, gamma} chi_{beta, gamma} P_beta X P_gamma with chi = processMatrix(Lambda), satisfies F(Lambda) = q_0(Lambda) = Q_0(Lambda) and sum_{w=0}^n Q_w(Lambda) = sum_beta q_beta(Lambda), is trace-preserving if and only if sum_{beta, gamma} chi_{beta, gamma} P_gamma P_beta = I (which implies sum_beta q_beta(Lambda) = sum_{w=0}^n Q_w(Lambda) = 1), has real nonnegative Pauli-twirl weights whenever Lambda is completely positive, and conversely every nonnegative weight vector q defines a completely positive Pauli channel that is trace-preserving when sum_beta q_beta = 1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-projector-unit-vector-iff-theorem",
                "Equivalence of projector and unit-vector single-qubit SICs",
                "isQubitSICProjector_iff_exists_unitVectorQubitSIC",
                ProjectorUnitVectorIffFormula(),
                "A family of four 2 by 2 complex matrices satisfies IsQubitSICProjector if and only if its members are the rank-one density matrices of four unit vectors in C^2 satisfying IsUnitVectorQubitSIC.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(SicSource)),
            Node("sickfidelity-matrices-and-per-qubit-traces-theorem",
                "Overlap-inverse matrices, 2-design moments, diagonal per-qubit functionals, and SIC-choice independence",
                "qubit_sic_matrices_and_per_qubit_traces",
                MatricesAndPerQubitTracesFormula(),
                "Establishes B(I_4 - A) = (I_4 - A)B = I_4 whereas the matrix with entries (1 - 5 delta_{i,j}) / 4 gives diagonal entries 7 / 4 in B(I_4 - A'); proves the n-qubit inverse expansion prod_i (I_4 - A)_{a_i, b_i} = sum_T (-1)^{|T|} (M_T)_{a, b} = (-1)^m 5^{n - m} / 4^n where m is the number of qubits with a_i != b_i; derives the single-qubit 2-design identities, sum_a rho_a = 2 I_2, e(0, 0) = 1, alpha(0, 0) = 0, and e(beta, beta) = alpha(beta, beta) = 1 / 3 for nonzero beta with off-diagonal vanishing; factors the n-qubit subset trace across T and its complement; and deduces that F_k(Lambda) depends only on the Pauli-twirl weights q_beta(Lambda), agrees with F_k of the Pauli-twirled map, and is independent of the chosen single-qubit SICs.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(SicSource)),
            Node("sickfidelity-pauli-weight-alternating-sum-theorem",
                "Universal Pauli-weight alternating binomial formula for SIC k-fidelities",
                "kFidelity_eq_pauliWeight_alternating_sum",
                PauliWeightAlternatingSumFormula(),
                "For every n, k, every choice of single-qubit SICs, and every complex-linear map Lambda on M_{2^n}(C), F_k(Lambda) = Q_0(Lambda) + (-1)^k sum_{w=1}^n 3^{-w} C(w - 1, k) Q_w(Lambda). Consequently F_k(Lambda) = F(Lambda) for all k >= n, F_0(Lambda) = sum_beta 3^{-|beta|} q_beta(Lambda), and for completely positive Lambda the complex k-fidelity equals its real projection with real weight sums.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("sickfidelity-cp-alternating-truncation-bound-theorem",
                "Alternating truncation error identity and support characterization for completely positive maps",
                "cp_kFidelity_alternating_truncation_bound",
                CpAlternatingTruncationBoundFormula(),
                "For every completely positive n-qubit map Lambda and every k, (-1)^k (F_k(Lambda) - F(Lambda)) = sum_{w=k+1}^n 3^{-w} C(w - 1, k) Q_w(Lambda) >= 0, yielding F_k(Lambda) <= F(Lambda) for odd k, F(Lambda) <= F_k(Lambda) for even k, F_j(Lambda) <= F_i(Lambda) for all odd j and even i, and equality F_k(Lambda) = F(Lambda) if and only if Q_w(Lambda) = 0 for all w >= k + 1, equivalently q_beta(Lambda) = 0 whenever |beta| > k.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Var(string x) => new Formula.Symbol(FormulaIdentifier.Create(x));
    private static Formula Field(string x) => Seq(Mathbb, Grp(F.Id(x)));
    private static Formula Named(string x) => Seq(Operatorname, Grp(F.Id(x)));
    private static Formula Fn(string name, params Formula[] args) => Call(name, args);
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Paren(Formula a) => Seq(Left, Open, a, Right, Close);
    private static Formula ProdType(Formula a, Formula b) => Seq(Left, Open, a, Sp, Times, Sp, b, Right, Close);
    private static Formula NegOf(Formula a) => new Formula.Negate(a);
    private static Formula FracOf(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Subscript(a, b);
    private static Formula Inv(Formula a) => Pow(a, NegOf(Num(1)));
    private static Formula Eqn(Formula a, Formula b) => Equal(a, b);
    private static Formula NeqRel(Formula a, Formula b) => NotEqual(a, b);
    private static Formula LtRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula MemRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Conj(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Conj3(Formula a, Formula b, Formula c) => Conj(a, Conj(b, c));
    private static Formula Conj4(Formula a, Formula b, Formula c, Formula d) => Conj(a, Conj3(b, c, d));
    private static Formula Conj5(Formula a, Formula b, Formula c, Formula d, Formula e) =>
        Conj(a, Conj4(b, c, d, e));
    private static Formula Conj6(Formula a, Formula b, Formula c, Formula d, Formula e, Formula f) =>
        Conj(a, Conj5(b, c, d, e, f));
    private static Formula Conj7(Formula a, Formula b, Formula c, Formula d, Formula e, Formula f, Formula g) =>
        Conj(a, Conj6(b, c, d, e, f, g));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffRel(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula SumIn(string x, Formula set, Formula body) =>
        Seq(Sub(Sum, MemRel(Var(x), set)), Sp, body);
    private static Formula ProdIn(string x, Formula set, Formula body) =>
        Seq(Sub(Prod, MemRel(Var(x), set)), Sp, body);
    private static Formula FilterSet(string x, Formula domain, Formula pred) =>
        Seq(Left, OpenBrace, MemRel(Var(x), domain), Sp, Mid, Sp, pred, Right, CloseBrace);
    private static Formula Ite(Formula cond, Formula t, Formula e) => Fn("ite", cond, t, e);
    private static Formula Fun2(string x, Formula dx, string y, Formula dy, Formula body) =>
        Paren(Seq(LambdaLower, Sp, MemRel(Var(x), dx), Comma, Sp, MemRel(Var(y), dy), Sp, Mapsto, Sp, body));

    private static Formula NatT => Field("N");
    private static Formula RealT => Field("R");
    private static Formula ComplexT => Field("C");
    private static Formula FinK(long k) => Fn("Fin", Num(k));
    private static Formula FinN(Formula n) => Fn("Fin", n);
    private static Formula QIdx(Formula n) => Fn("QubitIndex", n);
    private static Formula PLbl(Formula n) => Fn("PauliLabel", n);
    private static Formula QMap(Formula n) => Fn("QubitMap", n);
    private static Formula QMat => Named("QubitMatrix");
    private static Formula MatN(Formula n) => Fn("Matrix", QIdx(n), QIdx(n), ComplexT);
    private static Formula SicFam1 => Arrow(FinK(4), QMat);
    private static Formula SicFamN(Formula n) => Arrow(FinN(n), SicFam1);
    private static Formula Inv3 => Inv(Num(3));
    private static Formula Inv4 => Inv(Num(4));
    private static Formula Inv4Pow(Formula n) => Inv(Pow(Num(4), n));
    private static Formula NegOnePow(Formula k) => Pow(NegOf(Num(1)), k);

    private static Formula QubitIndexFormula()
    {
        var n = Var("n");
        return All("n", NatT, Eqn(QIdx(n), Arrow(FinN(n), FinK(2))));
    }

    private static Formula PauliLabelFormula()
    {
        var n = Var("n");
        return All("n", NatT, Eqn(PLbl(n), Arrow(FinN(n), FinK(4))));
    }

    private static Formula QubitMapFormula()
    {
        var n = Var("n");
        return All("n", NatT, Eqn(QMap(n), Fn("MatrixMap", QIdx(n), QIdx(n), ComplexT)));
    }

    private static Formula Pauli1Formula()
    {
        var yMat = Seq(Begin, Grp(F.Id("pmatrix")), Num(0), Sp, Amp, Sp, NegOf(Named("I")), Sp,
            RowBreak, Sp, Named("I"), Sp, Amp, Sp, Num(0), End, Grp(F.Id("pmatrix")));
        return Conj4(
            Eqn(Fn("pauli1", Num(0)), Num(1)),
            Eqn(Fn("pauli1", Num(1)), Named("qubitX")),
            Eqn(Fn("pauli1", Num(2)), yMat),
            Eqn(Fn("pauli1", Num(3)), Named("qubitZ")));
    }

    private static Formula PauliNFormula()
    {
        Formula n = Var("n"), b = Var("b"), x = Var("x"), y = Var("y"), i = Var("i");
        return All("n", NatT, All("b", PLbl(n), All("x", QIdx(n), All("y", QIdx(n),
            Eqn(At(Fn("pauliN", n, b), x, y),
                ProdIn("i", FinN(n), At(Fn("pauli1", At(b, i)), At(x, i), At(y, i))))))));
    }

    private static Formula HammingWeightFormula()
    {
        Formula n = Var("n"), b = Var("b"), i = Var("i");
        return All("n", NatT, All("b", PLbl(n),
            Eqn(Fn("hammingWeight", b),
                Fn("card", FilterSet("i", FinN(n), NeqRel(At(b, i), Num(0)))))));
    }

    private static Formula ProcessMatrixFormula()
    {
        Formula n = Var("n"), l = Var("L"), b = Var("b"), g = Var("g");
        Formula u = Var("u"), x = Var("x"), v = Var("v"), y = Var("y");
        var term = Multiply(Multiply(At(Fn("pauliN", n, b), x, u),
            At(At(l, Fn("single", x, y, Num(1))), u, v)), At(Fn("pauliN", n, g), v, y));
        var sums = SumIn("u", QIdx(n), SumIn("x", QIdx(n), SumIn("v", QIdx(n), SumIn("y", QIdx(n), term))));
        return All("n", NatT, All("L", QMap(n), All("b", PLbl(n), All("g", PLbl(n),
            Eqn(Fn("processMatrix", l, b, g), Multiply(Inv4Pow(n), sums))))));
    }

    private static Formula PauliTwirlWeightFormula()
    {
        Formula n = Var("n"), l = Var("L"), b = Var("b");
        return All("n", NatT, All("L", QMap(n), All("b", PLbl(n),
            Eqn(Fn("pauliTwirlWeight", l, b), Fn("processMatrix", l, b, b)))));
    }

    private static Formula PauliWeightSumFormula()
    {
        Formula n = Var("n"), l = Var("L"), w = Var("w"), b = Var("b"), c = Var("c");
        var fiber = FilterSet("c", PLbl(n), Eqn(Fn("hammingWeight", c), w));
        return All("n", NatT, All("L", QMap(n), All("w", NatT,
            Eqn(Fn("pauliWeightSum", l, w), SumIn("b", fiber, Fn("pauliTwirlWeight", l, b))))));
    }

    private static Formula MaxEntangledVecFormula()
    {
        Formula n = Var("n"), p = Var("p");
        var norm = Inv(Fn("sqrt", Pow(Num(2), n)));
        return All("n", NatT, All("p", ProdType(QIdx(n), QIdx(n)),
            Eqn(At(Fn("maxEntangledVec", n), p), Ite(Eqn(Fn("fst", p), Fn("snd", p)), norm, Num(0)))));
    }

    private static Formula MaxEntangledProjFormula()
    {
        var n = Var("n");
        var v = Fn("maxEntangledVec", n);
        return All("n", NatT, Eqn(Fn("maxEntangledProj", n), Fn("vecMulVec", v, Fn("star", v))));
    }

    private static Formula ProcessFidelityFormula()
    {
        Formula n = Var("n"), l = Var("L");
        var v = Fn("maxEntangledVec", n);
        var acted = At(Fn("kron", Named("id"), l), Fn("maxEntangledProj", n));
        return All("n", NatT, All("L", QMap(n),
            Eqn(Fn("processFidelity", l), Fn("dotProduct", Fn("star", v), Fn("mulVec", acted, v)))));
    }

    private static Formula PauliChannelFormula()
    {
        Formula n = Var("n"), q = Var("q"), xMat = Var("X"), b = Var("b");
        var pnb = Fn("pauliN", n, b);
        var conjTerm = Multiply(At(q, b), Multiply(Multiply(pnb, xMat), pnb));
        return All("n", NatT, All("q", Arrow(PLbl(n), RealT), All("X", MatN(n),
            Eqn(At(Fn("pauliChannel", q), xMat), SumIn("b", PLbl(n), conjTerm)))));
    }

    private static Formula ComplexPauliTwirlFormula()
    {
        Formula n = Var("n"), l = Var("L"), xMat = Var("X"), b = Var("b");
        var pnb = Fn("pauliN", n, b);
        var conjTerm = Multiply(Fn("pauliTwirlWeight", l, b), Multiply(Multiply(pnb, xMat), pnb));
        return All("n", NatT, All("L", QMap(n), All("X", MatN(n),
            Eqn(At(Fn("complexPauliTwirl", l), xMat), SumIn("b", PLbl(n), conjTerm)))));
    }

    private static Formula RealTwirlWeightFormula()
    {
        Formula n = Var("n"), l = Var("L"), b = Var("b");
        return All("n", NatT, All("L", QMap(n), All("b", PLbl(n),
            Eqn(Fn("realTwirlWeight", l, b), Fn("re", Fn("pauliTwirlWeight", l, b))))));
    }

    private static Formula RealWeightSumFormula()
    {
        Formula n = Var("n"), l = Var("L"), w = Var("w");
        return All("n", NatT, All("L", QMap(n), All("w", NatT,
            Eqn(Fn("realWeightSum", l, w), Fn("re", Fn("pauliWeightSum", l, w))))));
    }

    private static Formula RealProcessFidelityFormula()
    {
        Formula n = Var("n"), l = Var("L");
        return All("n", NatT, All("L", QMap(n),
            Eqn(Fn("realProcessFidelity", l), Fn("re", Fn("processFidelity", l)))));
    }

    private static Formula IsQubitSicProjectorFormula()
    {
        Formula r = Var("r"), a = Var("a"), b = Var("b");
        var ra = At(r, a);
        var rb = At(r, b);
        var proj = All("a", FinK(4), Conj3(
            Fn("IsHermitian", ra),
            Eqn(Multiply(ra, ra), ra),
            Eqn(Fn("trace", ra), Num(1))));
        var overlap = All("a", FinK(4), All("b", FinK(4),
            Imp(NeqRel(a, b), Eqn(Fn("trace", Multiply(ra, rb)), Inv3))));
        return All("r", SicFam1, IffRel(Fn("IsQubitSICProjector", r), Conj(proj, overlap)));
    }

    private static Formula IsUnitVectorQubitSicFormula()
    {
        Formula s = Var("s"), a = Var("a"), b = Var("b");
        var vecFam = Arrow(FinK(4), Arrow(FinK(2), ComplexT));
        var unit = All("a", FinK(4), Eqn(Fn("dotProduct", Fn("star", At(s, a)), At(s, a)), Num(1)));
        var pair = All("a", FinK(4), All("b", FinK(4),
            Imp(NeqRel(a, b),
                Eqn(Fn("normSq", Fn("dotProduct", Fn("star", At(s, a)), At(s, b))), Inv3))));
        return All("s", vecFam, IffRel(Fn("IsUnitVectorQubitSIC", s), Conj(unit, pair)));
    }

    private static Formula SicOverlapBFormula()
    {
        Formula a = Var("a"), b = Var("b");
        return All("a", FinK(4), All("b", FinK(4),
            Eqn(At(Named("sicOverlapB"), a, b), Ite(Eqn(a, b), Num(1), Inv3))));
    }

    private static Formula SicMatrixAFormula()
    {
        Formula a = Var("a"), b = Var("b");
        return All("a", FinK(4), All("b", FinK(4),
            Eqn(At(Named("sicMatrixA"), a, b), Ite(Eqn(a, b), NegOf(Inv4), Inv4))));
    }

    private static Formula ProductSicFormula()
    {
        Formula n = Var("n"), r = Var("r"), a = Var("a"), x = Var("x"), y = Var("y"), i = Var("i");
        return All("n", NatT, All("r", SicFamN(n), All("a", PLbl(n), All("x", QIdx(n), All("y", QIdx(n),
            Eqn(At(Fn("productSIC", r, a), x, y),
                ProdIn("i", FinN(n), At(At(At(r, i), At(a, i)), At(x, i), At(y, i)))))))));
    }

    private static Formula SicSubsetKernelFormula()
    {
        Formula n = Var("n"), tSet = Var("T"), a = Var("a"), b = Var("b"), i = Var("i");
        var idEntry = At(Sub(Named("I"), Num(4)), At(a, i), At(b, i));
        var factor = Ite(MemRel(i, tSet), At(Named("sicMatrixA"), At(a, i), At(b, i)), idEntry);
        return All("n", NatT, All("T", Fn("Finset", FinN(n)), All("a", PLbl(n), All("b", PLbl(n),
            Eqn(Fn("sicSubsetKernel", n, tSet, a, b), ProdIn("i", FinN(n), factor))))));
    }

    private static Formula KFidelityFormula()
    {
        Formula n = Var("n"), r = Var("r"), k = Var("k"), l = Var("L");
        Formula tSet = Var("T"), sSet = Var("S"), a = Var("a"), b = Var("b");
        var tFilter = FilterSet("S", Fn("Finset", FinN(n)), LeRel(Fn("card", sSet), k));
        var innerTerm = Multiply(Fn("sicSubsetKernel", n, tSet, a, b),
            Fn("trace", Multiply(Fn("productSIC", r, b), At(l, Fn("productSIC", r, a)))));
        var abSum = Paren(SumIn("a", PLbl(n), SumIn("b", PLbl(n), innerTerm)));
        var outer = SumIn("T", tFilter, Multiply(NegOnePow(Fn("card", tSet)), abSum));
        return All("n", NatT, All("r", SicFamN(n), All("k", NatT, All("L", QMap(n),
            Eqn(Fn("kFidelity", r, k, l), Multiply(Inv4Pow(n), outer))))));
    }

    private static Formula RealKFidelityFormula()
    {
        Formula n = Var("n"), r = Var("r"), k = Var("k"), l = Var("L");
        return All("n", NatT, All("r", SicFamN(n), All("k", NatT, All("L", QMap(n),
            Eqn(Fn("realKFidelity", r, k, l), Fn("re", Fn("kFidelity", r, k, l)))))));
    }

    private static Formula SicEFormula()
    {
        Formula r = Var("r"), b = Var("b"), g = Var("g"), a = Var("a");
        var prod = Multiply(Multiply(Multiply(At(r, a), Fn("pauli1", b)), At(r, a)), Fn("pauli1", g));
        return All("r", SicFam1, All("b", FinK(4), All("g", FinK(4),
            Eqn(Fn("sicE", r, b, g), Multiply(Inv4, SumIn("a", FinK(4), Fn("trace", prod)))))));
    }

    private static Formula SicAlphaFormula()
    {
        Formula r = Var("r"), u = Var("u"), v = Var("v"), a = Var("a"), b = Var("b");
        var prod = Multiply(Multiply(Multiply(At(r, b), Fn("pauli1", u)), At(r, a)), Fn("pauli1", v));
        var term = Multiply(At(Named("sicMatrixA"), a, b), Fn("trace", prod));
        return All("r", SicFam1, All("u", FinK(4), All("v", FinK(4),
            Eqn(Fn("sicAlpha", r, u, v), Multiply(Inv4, SumIn("a", FinK(4), SumIn("b", FinK(4), term)))))));
    }

    private static Formula PauliProcessCharacterizationFormula()
    {
        Formula n = Var("n"), l = Var("L"), xMat = Var("X"), b = Var("b"), g = Var("g");
        Formula c = Var("c"), w = Var("w"), q = Var("q");
        var pnb = Fn("pauliN", n, b);
        var png = Fn("pauliN", n, g);
        var expRhs = SumIn("b", PLbl(n), SumIn("g", PLbl(n),
            Multiply(Fn("processMatrix", l, b, g), Multiply(Multiply(pnb, xMat), png))));
        var cExpRhs = SumIn("b", PLbl(n), SumIn("g", PLbl(n),
            Multiply(At(c, b, g), Multiply(Multiply(pnb, xMat), png))));
        var c1 = All("L", QMap(n), Conj(
            All("X", MatN(n), Eqn(At(l, xMat), expRhs)),
            All("c", Arrow(PLbl(n), Arrow(PLbl(n), ComplexT)),
                Imp(All("X", MatN(n), Eqn(At(l, xMat), cExpRhs)),
                    All("b", PLbl(n), All("g", PLbl(n), Eqn(At(c, b, g), Fn("processMatrix", l, b, g))))))));
        var c2 = All("L", QMap(n), Conj3(
            Eqn(Fn("processFidelity", l), Fn("pauliTwirlWeight", l, Num(0))),
            Eqn(Fn("pauliWeightSum", l, Num(0)), Fn("pauliTwirlWeight", l, Num(0))),
            Eqn(SumIn("w", Fn("range", Add(n, Num(1))), Fn("pauliWeightSum", l, w)),
                SumIn("b", PLbl(n), Fn("pauliTwirlWeight", l, b)))));
        var tpCond = Eqn(SumIn("b", PLbl(n), SumIn("g", PLbl(n),
            Multiply(Fn("processMatrix", l, b, g), Multiply(png, pnb)))), Num(1));
        var c3 = All("L", QMap(n), Conj(
            IffRel(Fn("IsTracePreserving", l), tpCond),
            Imp(Fn("IsTracePreserving", l), Conj(
                Eqn(SumIn("b", PLbl(n), Fn("pauliTwirlWeight", l, b)), Num(1)),
                Eqn(SumIn("w", Fn("range", Add(n, Num(1))), Fn("pauliWeightSum", l, w)), Num(1))))));
        var c4 = All("L", QMap(n), Imp(Fn("IsCompletelyPositive", l), Conj3(
            All("b", PLbl(n), Conj(
                Eqn(Fn("im", Fn("pauliTwirlWeight", l, b)), Num(0)),
                LeRel(Num(0), Fn("re", Fn("pauliTwirlWeight", l, b))))),
            All("w", NatT, Conj(
                Eqn(Fn("ofReal", Fn("realWeightSum", l, w)), Fn("pauliWeightSum", l, w)),
                LeRel(Num(0), Fn("realWeightSum", l, w)))),
            Eqn(Fn("ofReal", Fn("realProcessFidelity", l)), Fn("processFidelity", l)))));
        var pch = Fn("pauliChannel", q);
        var c5 = All("q", Arrow(PLbl(n), RealT), Conj3(
            All("b", PLbl(n), All("g", PLbl(n),
                Eqn(Fn("processMatrix", pch, b, g), Ite(Eqn(b, g), Fn("ofReal", At(q, b)), Num(0))))),
            Imp(All("b", PLbl(n), LeRel(Num(0), At(q, b))), Fn("IsCompletelyPositive", pch)),
            Imp(Eqn(SumIn("b", PLbl(n), At(q, b)), Num(1)), Fn("IsTracePreserving", pch))));
        return All("n", NatT, Conj5(c1, c2, c3, c4, c5));
    }

    private static Formula ProjectorUnitVectorIffFormula()
    {
        Formula r = Var("r"), s = Var("s"), a = Var("a");
        var vecFam = Arrow(FinK(4), Arrow(FinK(2), ComplexT));
        return All("r", SicFam1, IffRel(
            Fn("IsQubitSICProjector", r),
            Ex("s", vecFam, Conj(
                Fn("IsUnitVectorQubitSIC", s),
                All("a", FinK(4), Eqn(At(r, a), Fn("rankOneDensity", At(s, a))))))));
    }

    private static Formula MatricesAndPerQubitTracesFormula()
    {
        Formula n = Var("n"), a = Var("a"), b = Var("b"), c = Var("c"), g = Var("g");
        Formula i = Var("i"), j = Var("j"), k = Var("k"), l = Var("L");
        Formula r = Var("r"), s = Var("s"), tSet = Var("T"), sSet = Var("S");
        Formula u = Var("u"), v = Var("v"), x = Var("x"), y = Var("y");
        Formula xMat = Var("X"), yMat = Var("Y");
        var matB = Named("sicOverlapB");
        var matA = Named("sicMatrixA");
        var oneMinusA = Subtract(Num(1), matA);
        var c1 = Conj(Eqn(Multiply(matB, oneMinusA), Num(1)), Eqn(Multiply(oneMinusA, matB), Num(1)));
        var altMat = Fn("matrixOf", Fun2("i", FinK(4), "j", FinK(4),
            FracOf(Subtract(Num(1), Ite(Eqn(i, j), Num(5), Num(0))), Num(4))));
        var c2 = All("a", FinK(4),
            Eqn(At(Multiply(matB, Subtract(Num(1), altMat)), a, a), FracOf(Num(7), Num(4))));
        var prodInv = ProdIn("i", FinN(n), At(oneMinusA, At(a, i), At(b, i)));
        var diffCard = Fn("card", FilterSet("i", FinN(n), NeqRel(At(a, i), At(b, i))));
        var closedInv = FracOf(
            Multiply(NegOnePow(diffCard), Pow(Num(5), Subtract(n, diffCard))),
            Pow(Num(4), n));
        var c3 = All("a", PLbl(n), All("b", PLbl(n), Conj(
            Eqn(prodInv, SumIn("T", Fn("Finset", FinN(n)),
                Multiply(NegOnePow(Fn("card", tSet)), Fn("sicSubsetKernel", n, tSet, a, b)))),
            Eqn(prodInv, closedInv))));
        var twoThirds = FracOf(Num(2), Num(3));
        var designEntry = All("u", FinK(2), All("v", FinK(2), All("x", FinK(2), All("y", FinK(2),
            Eqn(SumIn("a", FinK(4), Multiply(At(At(r, a), u, x), At(At(r, a), v, y))),
                Multiply(twoThirds, Add(
                    Ite(Conj(Eqn(u, x), Eqn(v, y)), Num(1), Num(0)),
                    Ite(Conj(Eqn(u, y), Eqn(v, x)), Num(1), Num(0)))))))));
        var designTrace = All("X", QMat, All("Y", QMat,
            Eqn(SumIn("a", FinK(4),
                    Multiply(Fn("trace", Multiply(At(r, a), xMat)), Fn("trace", Multiply(At(r, a), yMat)))),
                Multiply(twoThirds, Add(Fn("trace", Multiply(xMat, yMat)),
                    Multiply(Fn("trace", xMat), Fn("trace", yMat)))))));
        var c4 = All("r", SicFam1, Imp(Fn("IsQubitSICProjector", r), Conj5(
            designEntry,
            Eqn(SumIn("a", FinK(4), At(r, a)), Multiply(Num(2), Sub(Named("I"), Num(2)))),
            designTrace,
            All("b", FinK(4), All("g", FinK(4),
                Eqn(Fn("sicE", r, b, g), Ite(Eqn(b, g), Ite(Eqn(b, Num(0)), Num(1), Inv3), Num(0))))),
            All("b", FinK(4), All("g", FinK(4),
                Eqn(Fn("sicAlpha", r, b, g), Ite(Eqn(b, g), Ite(Eqn(b, Num(0)), Num(0), Inv3), Num(0))))))));
        var prodTrace = Fn("trace", Multiply(Multiply(Multiply(
            Fn("productSIC", r, c), Fn("pauliN", n, b)), Fn("productSIC", r, a)), Fn("pauliN", n, g)));
        var c5 = All("r", SicFamN(n), All("T", Fn("Finset", FinN(n)), All("b", PLbl(n), All("g", PLbl(n),
            Eqn(Multiply(Inv4Pow(n), SumIn("a", PLbl(n), SumIn("c", PLbl(n),
                    Multiply(Fn("sicSubsetKernel", n, tSet, a, c), prodTrace)))),
                ProdIn("i", FinN(n), Ite(MemRel(i, tSet),
                    Fn("sicAlpha", At(r, i), At(b, i), At(g, i)),
                    Fn("sicE", At(r, i), At(b, i), At(g, i)))))))));
        var localR = All("i", FinN(n), Fn("IsQubitSICProjector", At(r, i)));
        var localS = All("i", FinN(n), Fn("IsQubitSICProjector", At(s, i)));
        var tFilter = FilterSet("S", Fn("Finset", FinN(n)), LeRel(Fn("card", sSet), k));
        var tFactor = Multiply(Multiply(NegOnePow(Fn("card", tSet)),
            Paren(ProdIn("i", tSet, Fn("sicAlpha", At(r, i), At(b, i), At(b, i))))),
            Paren(ProdIn("i", Pow(tSet, F.Id("c")), Fn("sicE", At(r, i), At(b, i), At(b, i)))));
        var c6 = All("r", SicFamN(n), Imp(localR, All("k", NatT, All("L", QMap(n), Conj(
            Eqn(Fn("kFidelity", r, k, l),
                SumIn("b", PLbl(n), Multiply(Fn("pauliTwirlWeight", l, b), Paren(SumIn("T", tFilter, tFactor))))),
            Eqn(Fn("kFidelity", r, k, l), Fn("kFidelity", r, k, Fn("complexPauliTwirl", l))))))));
        var c7 = All("r", SicFamN(n), All("s", SicFamN(n), Imp(localR, Imp(localS,
            All("k", NatT, All("L", QMap(n), Eqn(Fn("kFidelity", r, k, l), Fn("kFidelity", s, k, l))))))));
        return All("n", NatT, Conj7(c1, c2, c3, c4, c5, c6, c7));
    }

    private static Formula PauliWeightAlternatingSumFormula()
    {
        Formula n = Var("n"), k = Var("k"), r = Var("r"), l = Var("L");
        Formula i = Var("i"), w = Var("w"), b = Var("b");
        var localR = All("i", FinN(n), Fn("IsQubitSICProjector", At(r, i)));
        var coeff = Multiply(Pow(Inv3, w), Fn("choose", Subtract(w, Num(1)), k));
        var complexRhs = Add(Fn("pauliWeightSum", l, Num(0)),
            Multiply(NegOnePow(k), SumIn("w", Fn("Icc", Num(1), n), Multiply(coeff, Fn("pauliWeightSum", l, w)))));
        var realRhs = Add(Fn("realWeightSum", l, Num(0)),
            Multiply(NegOnePow(k), SumIn("w", Fn("Icc", Num(1), n), Multiply(coeff, Fn("realWeightSum", l, w)))));
        var zeroSum = SumIn("b", PLbl(n),
            Multiply(Pow(Inv3, Fn("hammingWeight", b)), Fn("pauliTwirlWeight", l, b)));
        var body = Conj4(
            Eqn(Fn("kFidelity", r, k, l), complexRhs),
            Imp(LeRel(n, k), Eqn(Fn("kFidelity", r, k, l), Fn("processFidelity", l))),
            Eqn(Fn("kFidelity", r, Num(0), l), zeroSum),
            Imp(Fn("IsCompletelyPositive", l), Conj(
                Eqn(Fn("ofReal", Fn("realKFidelity", r, k, l)), Fn("kFidelity", r, k, l)),
                Eqn(Fn("realKFidelity", r, k, l), realRhs))));
        return All("n", NatT, All("k", NatT, All("r", SicFamN(n), Imp(localR, All("L", QMap(n), body)))));
    }

    private static Formula CpAlternatingTruncationBoundFormula()
    {
        Formula n = Var("n"), k = Var("k"), r = Var("r"), l = Var("L");
        Formula i = Var("i"), j = Var("j"), w = Var("w"), b = Var("b");
        var localR = All("i", FinN(n), Fn("IsQubitSICProjector", At(r, i)));
        var fk = Fn("realKFidelity", r, k, l);
        var fp = Fn("realProcessFidelity", l);
        var tailRange = Fn("Icc", Add(k, Num(1)), n);
        var coeff = Multiply(Pow(Inv3, w), Fn("choose", Subtract(w, Num(1)), k));
        var tailSum = SumIn("w", tailRange, Multiply(coeff, Fn("realWeightSum", l, w)));
        var eqChar = Conj(
            IffRel(Eqn(fk, fp), All("w", tailRange, Eqn(Fn("realWeightSum", l, w), Num(0)))),
            IffRel(Eqn(fk, fp), All("b", PLbl(n),
                Imp(LtRel(k, Fn("hammingWeight", b)), Eqn(Fn("realTwirlWeight", l, b), Num(0))))));
        var body = Conj6(
            Eqn(Multiply(NegOnePow(k), Subtract(fk, fp)), tailSum),
            LeRel(Num(0), tailSum),
            Imp(Fn("Odd", k), LeRel(fk, fp)),
            Imp(Fn("Even", k), LeRel(fp, fk)),
            All("i", NatT, All("j", NatT, Imp(Fn("Odd", j), Imp(Fn("Even", i),
                LeRel(Fn("realKFidelity", r, j, l), Fn("realKFidelity", r, i, l)))))),
            eqChar);
        return All("n", NatT, All("k", NatT, All("r", SicFamN(n),
            Imp(localR, All("L", QMap(n), Imp(Fn("IsCompletelyPositive", l), body))))));
    }
}
