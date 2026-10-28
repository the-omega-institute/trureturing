using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class NonlocalityDepthQuantumBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/bernards2023nonlocalitydepth");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n >= 3, the Bernards--Gühne Bell functional has exact quantum maximum sqrt(2) n 2^(n-2), over all finite local dimensions, binary observables and density matrices.",
        H("The exact quantum bound for nonlocality depth"),
        Blocks(
            Node("expectation_upper", "An operator bound controls every density expectation", ExpectationUpperFormula(),
                "If q times the identity minus B is positive semidefinite, then the real trace pairing of B with any positive semidefinite trace-one matrix is at most q.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("tensor_star", "Adjoints commute with the tensor product", TensorStarFormula(),
                "The tensor product of the adjoints of a finite family of complex matrices equals the adjoint of their tensor product. The local matrix carriers may be arbitrary types.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("IsBinaryObservable", "Binary observables", BinaryObservableFormula(),
                "A binary observable is Hermitian and both its shifts 1 - M and 1 + M are positive semidefinite. The Bell maximum ranges over two such observables at each party.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("one_add_posSemidef_of_contraction", "The positive shift of a Hermitian contraction", ContractionFormula(),
                "For a Hermitian matrix C, positivity of 1 - C conjugate-transpose times C implies positivity of 1 + C. Adding the positive square of 1 + C to the contraction defect gives twice 1 + C. This implication gives positivity of both shifts of an involution and of the diagonal blocks in the separable scalar-shift construction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Describe.Lean(DescribeId.Create("nonlocality-quantum-upper-involution-binary"),
                DeclarationHandle.Create(Prefix + "involution_binary"),
                H("Both shifts of a Hermitian involution are positive"),
                StatementSource.FromAuthor(InvolutionBinaryFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Hermitian matrix whose square is the identity has positive semidefinite shifts 1 - A and 1 + A."))), DescribeRole.Lemma),
            Node("bellOp", "The Bell polynomial of Eq. (28)", BellFormula(),
                "Section III.F, PDF p. 5, Eq. (28), reads: “F_n = ∑_{ℓ=1}^n (−1)^{1+⌈ℓ/2⌉} ℓ (1…1 2…2) ≤ n 2^{n−2}.” The bracket sums the distinct party permutations, with n - ℓ settings 1 and ℓ settings 2. Each Boolean setting string therefore occurs once. Its weight hammingDist(x,fun j ↦ false) counts the true coordinates. The integer sign phase(h) is the sign (-1)^(1+ceil(h/2)) defined in HybridMerminDepthBound.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The exact maximum in every party number", ClaimFormula(),
                "Section III.F, PDF p. 5, Eq. (29), states verbatim: “In the following, we discuss numerical findings concerning the Bell inequalities F_n for n ≤ 8 parties. We find, that the quantum bound of the inequalities is F_n = √2 n 2^{n−2} (29) up to numerical precision, which is achieved by choosing A₁ = B₁ = … = σ_x and A₂ = B₂ = … = σ_z”. The assertion extends this value to every n >= 3. Fin n labels parties; d gives their arbitrary finite local dimensions. A assigns two local observables per party, and rho ranges over positive-semidefinite matrices of trace one. IsGreatest asserts both the upper bound and its attainment. Nat.sub denotes truncated natural-number subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Upper.unweighted", "The shifted unweighted polynomial", UnweightedFormula(),
                "The natural number shift r changes the phase of the coefficient sequence. Removing one party splits this polynomial into its two local settings, with shifts r and r + 1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("Upper.unweighted_bound", "The all-party shifted operator estimate", BoundFormula(),
                "The identity phase(h + 2) = -phase(h) makes the two-party polynomial a signed CHSH operator. Mathlib's Tsirelson inequality gives its positive-semidefinite upper bound 2 sqrt(2). For a Hermitian involution A and a matrix B bounded on both sides by q, the positive tensor sum ((1 + A) tensor (q - B) + (1 - A) tensor (q + B))/2 equals q - A tensor B. Applying this identity to the two terms in the party split propagates the estimate by induction. The statement includes all natural number shifts and every finite local carrier.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("result", "The universal upper bound is attained", Disp(X("claim")),
                "Distributing the Hamming weight over the marked parties writes bellOp as a sum of n terms. Each term consists of a local observable at setting true tensored with a shifted unweighted polynomial on the other n - 1 parties. The shifted estimate bounds each term by sqrt(2) 2^(n-2), and addition gives sqrt(2) n 2^(n-2). A Hermitian contraction dilates to the involution with blocks A, sqrt(1 - A²), sqrt(1 - A²), -A. Compression preserves every correlator, so the same bound holds for all binary observables. Positivity of the trace of a product of positive-semidefinite matrices gives the expectation bound for every density matrix. For attainment take X and Y at every party. On the two constant basis strings the off-diagonal amplitude is n 2^(n-2)(-1 + i). The normalized vector (e0 + eta e1)/sqrt(2), with eta = (-1 + i)/sqrt(2), is an eigenvector with the positive maximal eigenvalue. Its rank-one density matrix attains the bound.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bernards-guhne-2023-nonlocality-depth-quantum-bound"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("nonlocality-quantum-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name.Replace("Upper.", "")), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(X(name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Numbers(string name) => Seq(Mathbb, Grp(X(name)));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula Family(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Parenthesized(Seq(X(name), Colon, type)), Sp, To, Sp, body));
    private static Formula Cast(Formula value, string type) => Parenthesized(Seq(value, Colon, Numbers(type)));
    private static Formula Matrix(Formula type) => Call("Matrix", type, type, Numbers("C"));
    private static Formula SigmaType(Formula n) => Arrow(Fin(n), X("Type"));
    private static Formula Index(Formula n) => Family("j", Fin(n), Call("sigma", X("j")));
    private static Formula Settings(Formula n) => Arrow(Fin(n), X("Bool"));
    private static Formula Observables(Formula n) => Family("j", Fin(n), Arrow(X("Bool"), Matrix(Call("sigma", X("j")))));
    private static Formula Instances(Formula n, string name) =>
        Seq(OpenBracket, All("j", Fin(n), Call(name, Call("sigma", X("j")))), CloseBracket, Sp);
    private static Formula Weight(Formula x, Formula n) => Call("hammingDist", x, At(Q("Function", "const"), Fin(n), X("false")));
    private static Formula Big(string name, Formula token, Formula type, Formula body) =>
        Seq(token, Underscore, Grp(X(name), Colon, type), Sp, Parenthesized(body));
    private static Formula PSD(Formula value) => At(Q("Matrix", "PosSemidef"), value);
    private static Formula Hermitian(Formula value) => At(Q("Matrix", "IsHermitian"), value);
    private static Formula Trace(Formula value) => At(Q("Matrix", "trace"), value);
    private static Formula Smul(Formula a, Formula b) => At(Q("SMul", "smul"), a, b);

    private static Formula ExpectationUpperFormula()
    {
        Formula m = X("m"), rho = X("rho"), b = X("B"), q = X("q");
        return Disp(All("m", X("Type"), Seq(
            OpenBracket, Call("Fintype", m), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", m), CloseBracket, Sp,
            All("rho", Matrix(m), All("B", Matrix(m), All("q", Numbers("R"),
                Implies(And(PSD(rho), Equal(Trace(rho), D(1))),
                    Implies(PSD(Sub(Smul(q, D(1)), b)),
                        Le(At(Q("Complex", "re"), Trace(Mul(rho, b))), q)))))))));
    }

    private static Formula TensorStarFormula()
    {
        Formula n = X("n"), sigma = X("sigma"), matrices = X("M"), j = X("j");
        Formula local = Matrix(At(sigma, j));
        Formula family = Family("j", Fin(n), local);
        Formula adjoints = Parenthesized(Seq(LambdaLower, Sp,
            Parenthesized(Seq(j, Sp, Colon, Sp, Fin(n))), Sp, Mapsto, Sp,
            At(Q("Matrix", "conjTranspose"), At(matrices, j))));
        Formula left = At(Q("ProductPrefixRigidity", "productMap"), sigma, adjoints);
        Formula right = At(Q("Matrix", "conjTranspose"), At(Q("ProductPrefixRigidity", "productMap"), sigma, matrices));
        return Disp(All("n", Numbers("N"), All("sigma", Arrow(Fin(n), X("Type")),
            Seq(Instances(n, "Fintype"), Instances(n, "DecidableEq"),
                All("M", family, Equal(left, right))))));
    }

    private static Formula BinaryObservableFormula()
    {
        Formula m = X("m"), matrix = X("M");
        Formula body = And(Hermitian(matrix),
            And(PSD(Sub(D(1), matrix)), PSD(Add(D(1), matrix))));
        return Disp(All("m", Numbers("N"), All("M", Matrix(Fin(m)),
            new Formula.Logic(Call("IsBinaryObservable", matrix), FormulaLogicOperator.Iff, body))));
    }

    private static Formula ContractionFormula()
    {
        Formula iota = X("iota"), c = X("C");
        Formula adjoint = At(Q("Matrix", "conjTranspose"), c);
        return Disp(All("iota", X("Type"), Seq(
            OpenBracket, Call("Fintype", iota), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", iota), CloseBracket, Sp,
            All("C", Matrix(iota), Implies(Hermitian(c),
                Implies(PSD(Sub(D(1), Mul(adjoint, c))), PSD(Add(D(1), c))))))));
    }

    private static Formula InvolutionBinaryFormula()
    {
        Formula m = X("m"), a = X("A");
        return Disp(All("m", X("Type"), Seq(
            OpenBracket, Call("Fintype", m), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", m), CloseBracket, Sp,
            All("A", Matrix(m), Implies(Hermitian(a),
                Implies(Equal(Pow(a, D(2)), D(1)),
                    And(PSD(Sub(D(1), a)), PSD(Add(D(1), a)))))))));
    }

    private static Formula BellFormula()
    {
        Formula n = X("n"), h = Weight(X("x"), n);
        Formula coefficient = Cast(Mul(Cast(h, "Z"), Call("phase", h)), "C");
        Formula entry = Big("j", Prod, Fin(n), At(At(X("A"), X("j"), At(X("x"), X("j"))),
            At(X("a"), X("j")), At(X("b"), X("j"))));
        Formula tensor = Parenthesized(Seq(LambdaLower, Sp, X("a"), Sp, X("b"), Sp, Mapsto, Sp, entry));
        Formula rhs = Big("x", Sum, Settings(n), Smul(coefficient, tensor));
        Formula local = Family("j", Fin(n), Arrow(X("Bool"), Matrix(Fin(At(X("d"), X("j"))))));
        return Disp(All("n", Numbers("N"), All("d", Arrow(Fin(n), Numbers("N")),
            All("A", local, Equal(Call("bellOp", n, X("A")), rhs)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = X("n"), j = X("j"), rho = X("rho"), d = X("d");
        Formula local = Family("j", Fin(n), Arrow(X("Bool"), Matrix(Fin(At(d, j)))));
        Formula index = Family("j", Fin(n), Fin(At(d, j)));
        Formula observable = At(X("A"), j, X("s"));
        Formula binary = All("j", Fin(n), All("s", X("Bool"),
            Call("IsBinaryObservable", observable)));
        Formula density = And(PSD(rho), Equal(Trace(rho), D(1)));
        Formula expectation = At(Q("Complex", "re"), Trace(Mul(rho, Call("bellOp", n, X("A")))));
        Formula membership = Ex("d", Arrow(Fin(n), Numbers("N")), Ex("A", local, Ex("rho", Matrix(index),
            And(binary, And(density, Equal(X("v"), expectation))))));
        Formula set = Seq(OpenBrace, X("v"), Colon, Numbers("R"), Sp, Mid, Sp, membership, CloseBrace);
        Formula maximum = Mul(Mul(At(Q("Real", "sqrt"), D(2)), Cast(n, "R")), Pow(D(2), At(Q("Nat", "sub"), n, D(2))));
        Formula body = All("n", Numbers("N"), Implies(Le(D(3), n), Call("IsGreatest", set, maximum)));
        return Disp(new Formula.Logic(X("claim"), FormulaLogicOperator.Iff, body));
    }

    private static Formula UnweightedFormula()
    {
        Formula n = X("n"), r = X("r");
        Formula coefficient = Cast(Call("phase", Add(Weight(X("x"), n), r)), "C");
        Formula entry = Big("j", Prod, Fin(n), At(At(X("A"), X("j"), At(X("x"), X("j"))),
            At(X("a"), X("j")), At(X("b"), X("j"))));
        Formula tensor = Seq(LambdaLower, Sp, X("a"), Sp, X("b"), Sp, Mapsto, Sp, entry);
        Formula rhs = Big("x", Sum, Settings(n),
            Smul(coefficient, Parenthesized(Seq(Parenthesized(tensor), Colon, Matrix(Index(n))))));
        return Disp(All("n", Numbers("N"), All("sigma", SigmaType(n), Seq(Instances(n, "Fintype"),
            All("A", Observables(n), All("r", Numbers("N"), Equal(At(Q("Upper", "unweighted"), X("A"), r), rhs)))))));
    }

    private static Formula BoundFormula()
    {
        Formula k = X("k"), n = Add(k, D(2)), a = X("A"), j = X("j"), s = X("s"), r = X("r");
        Formula hermitian = All("j", Fin(n), All("s", X("Bool"), Hermitian(At(a, j, s))));
        Formula involution = All("j", Fin(n), All("s", X("Bool"), Equal(Pow(At(a, j, s), D(2)), D(1))));
        Formula scale = Mul(At(Q("Real", "sqrt"), D(2)), Pow(D(2), Add(k, D(1))));
        Formula identity = Parenthesized(Seq(D(1), Colon, Matrix(Index(n))));
        Formula estimate = PSD(Sub(Smul(scale, identity), At(Q("Upper", "unweighted"), a, r)));
        return Disp(All("k", Numbers("N"), All("sigma", SigmaType(n), Seq(Instances(n, "Fintype"), Instances(n, "DecidableEq"),
            All("A", Observables(n), Implies(hermitian, Implies(involution, All("r", Numbers("N"), estimate))))))));
    }
}
