using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AnticoherenceTraceDistanceRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/denisetal2026anticoherencemixed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A covariant spin-four channel decreases order-seven trace-distance anticoherence.",
        H("Trace-distance anticoherence need not increase under covariant noise"),
        Blocks(
            Node("spinAction", "The spin representation in Dicke coordinates", SpinAction(),
                "Embed spin n/2 into n qubits by the normalized Dicke embedding, apply n copies of the single-qubit special unitary matrix u, and compress back to Dicke coordinates. "
                    + "This gives a matrix of size n plus one. The symmetric-subspace interpretation is the one in arxiv.tex, lines 150–161; the displayed compression specifies its coordinates.",
                AssessedProvenance.FromRepo(Source)),
            Node("reducedState", "The reduced state in symmetric coordinates", ReducedState(),
                "For t at most n, embed the matrix into n qubits, group the first t coordinates and the last n minus t coordinates by appending the two words, and trace over the second group. "
                    + "Compression by the t-qubit Dicke embedding expresses the result in the symmetric t-qubit basis. "
                    + "The equivalence e includes the equality t plus (n minus t) equals n. The subscript on Equiv.cast specifies the resulting equality of word types; its proof supplies only type transport. "
                    + "For t greater than n the definition is zero. "
                    + "This is the reduced-state notion of arxiv.tex, lines 150–161, with the full mixed-state range specified at line 178.",
                AssessedProvenance.FromLiterature(Source)),
            Node("normalizer", "The largest distance from the maximally mixed state", Normalizer(),
                "The maximally mixed reference is the identity divided by t plus one. Take the supremum of its trace norm distances from all positive semidefinite matrices of trace one on the symmetric t-qubit space. "
                    + "This expresses the normalization K_t of arxiv.tex, lines 333–337, using a real supremum. It uses the full Schatten one-norm, without a factor of one half.",
                AssessedProvenance.FromLiterature(Source)),
            Node("anticoherence", "The Schatten-one distance candidate", Anticoherence(),
                "Subtract from one the trace norm distance of the t-qubit reduction from the maximally mixed symmetric state, divided by the normalizer. "
                    + "This is the distance candidate of arxiv.tex, lines 338–358, at Schatten exponent one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsCovariantChannel", "Complete positivity, trace preservation and spin covariance", CovariantChannel(),
                "A complex-linear matrix map is required to be completely positive and trace preserving, and to commute with conjugation by spinAction n u for every single-qubit special unitary matrix u and every input matrix x. "
                    + "This is the covariant-channel notion in arxiv.tex, lines 186–198, expressed on the full matrix algebra.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Trace-distance monotonicity for every mixed-state order", Claim(),
                "For every natural n at least one and every order t between one and n, the assertion requires anticoherence to increase or stay constant under every covariant channel on spin n/2 and every positive semidefinite input of trace one. "
                    + "It is the trace-distance reading of axiom (T4) at arxiv.tex, lines 186–198 and 363. The mixed-state range is the full range at line 178, including t greater than n/2.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("anticoherence-trace-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A spin-four counterexample at order seven"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                ResultArgument(),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("denis-lacaille-martin-serrano-ensastiga-2026-anticoherence-trace-distance"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("anticoherence-trace-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static BlockSequence ResultArgument() => Blocks(
        Paragraph(Text(
            "Use n equal to 8 and t equal to 7, and let Jx, Jy and Jz be the spin-four matrices in the Dicke basis indexed by r from 0 to 8, with Jz diagonal entry 4 minus r. "
                + "Let J+ be the raising matrix and put c = sqrt(3/3080). The five Kraus matrices, in order, are "
                + "(3 Jz squared minus 20 I)/sqrt(1540), minus c times (Jz J+ plus J+ Jz), "
                + "c times (Jz J+ adjoint plus J+ adjoint Jz), c times J+ squared, and c times (J+ adjoint) squared. "
                + "Let Phi(X) be the sum of K X K adjoint over these five matrices.")),
        Paragraph(Text(
            "Their nonzero entries shift the input index by 0, minus 1, 1, minus 2 and 2, respectively. "
                + "For z = 4 minus r, the squared amplitudes are (3z squared minus 20) squared divided by 1540; "
                + "3(2z plus 1) squared times (20 minus z(z plus 1)) divided by 3080; "
                + "3(2z minus 1) squared times (20 minus (z minus 1)z) divided by 3080; "
                + "3(20 minus z(z plus 1))(20 minus (z plus 1)(z plus 2)) divided by 3080; "
                + "and 3(20 minus (z minus 1)z)(20 minus (z minus 2)(z minus 1)) divided by 3080. "
                + "Different input columns have disjoint supports for each Kraus matrix. Summing the squared amplitudes in each column gives one, so the sum of K adjoint K is I.")),
        Paragraph(Text(
            "Choose rho = diag(209, 92, 560, 0, 441, 0, 294, 168, 0)/1764. "
                + "Its entries are nonnegative and sum to one, so it is positive semidefinite with trace one. "
                + "The same sparse-entry calculation, now summing over input columns, gives "
                + "Phi(rho) = diag(22288, 30100, 25528, 13149, 45540, 10584, 24654, 11613, 10584)/194040.")),
        Paragraph(Text(
            "To relate these spin coordinates to qubits, identify words with the same number of ones by permutations of their sites. "
                + "There are Nat.choose n r such words of weight r. Their normalized indicator vectors are the Dicke columns, whose Gram matrix is the identity. "
                + "A constant tensor power sends a Dicke column to a vector constant on each weight class. "
                + "The Dicke projector therefore fixes this image, so the tensor action intertwines with spinAction. "
                + "Splitting a weight-r Dicke column between t and n minus t sites gives, at weights k and l with k plus l equal to r, "
                + "the coefficient sqrt(Nat.choose t k times Nat.choose (n minus t) l) divided by sqrt(Nat.choose n r), and zero otherwise. "
                + "Apply CoherentHistorySchmidt.normalized_coefficient_factorization to the binary occupation multiset and identify its sector vectors with the Dicke columns. "
                + "The sector multiplicities become binomial coefficients by sector_words_card_multinomial and Nat.binomial_eq_choose, giving the factorization through the two smaller Dicke embeddings. "
                + "The partial-trace identity for product embeddings removes the isometry on the traced factor; compression by the remaining isometry gives exactly reducedState.")),
        Paragraph(Text(
            "The ladder identity J+ J+ adjoint plus J+ adjoint J+ = 40 I minus 2 Jz squared implies that the sum of Jx squared, Jy squared and Jz squared is 20 I. "
                + "For axes a,b in {x,y,z}, set S_ab = (Ja Jb plus Jb Ja)/2 minus (20/3) delta_ab I. "
                + "These matrices are Hermitian, symmetric in a,b, and have S_xx plus S_yy plus S_zz equal to zero. "
                + "Expressing the five Kraus matrices in these Cartesian components and expanding their sandwiches gives "
                + "Phi(X) = (3/770) times the sum of S_ab X S_ab over all nine ordered pairs of axes.")),
        Paragraph(Text(
            "The tensor power is unitary, and its intertwining with the isometric Dicke embedding makes spinAction unitary. "
                + "The single-site Dicke sum identifies the three spin-four matrices with the compressions of collectiveSpin 8. "
                + "For every special unitary qubit matrix u, Pauli conjugation gives a real orthogonal matrix r. "
                + "Collective tensor rotation and the Dicke intertwining then give D Ja D adjoint = sum_c r_ac Jc, where D = spinAction 8 u. "
                + "Quadratic rotation gives D S_ab D adjoint = sum_ce r_ac r_be S_ce. "
                + "The Kronecker product of r with itself is orthogonal, so the orthogonal sandwich identity preserves the Cartesian sum. "
                + "Thus Phi(D X D adjoint) = D Phi(X) D adjoint for every X. "
                + "The Kraus form supplies complete positivity and the column identity supplies trace preservation, proving all three channel conditions.")),
        Paragraph(Text(
            "For a real diagonal input with entries p_r, the splitting coefficients make the reduced matrix diagonal. Its k-th entry is "
                + "the sum over r of p_r times Nat.choose t k times Nat.choose (n minus t) (r minus k), divided by Nat.choose n r, "
                + "with an additional factor one when k is at most r and zero otherwise; r minus k is natural-number subtraction. "
                + "At n = 8 and t = 7 this gives "
                + "reducedState 7 rho = diag(21, 21, 40, 21, 21, 21, 21, 2)/168 and "
                + "reducedState 7 (Phi(rho)) = diag(69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095)/517440. "
                + "Subtract I/8 and sum the absolute values of the diagonal entries. The two trace norms are respectively 19/84 and 3933/17248.")),
        Paragraph(Text(
            "The normalizer at order seven is positive. Indeed, the maximally mixed matrix is positive semidefinite of trace one, "
                + "and every such matrix has trace norm one. The triangle inequality bounds every distance in the defining supremum by two. "
                + "The rank-one diagonal state diag(1,0,0,0,0,0,0,0) has distance 7/4 from I/8, so 7/4 is at most normalizer 7.")),
        Paragraph(Text(
            "Finally assume claim and apply it to this channel and rho at n = 8 and t = 7. "
                + "It would give 1 minus (19/84)/(normalizer 7) at most 1 minus (3933/17248)/(normalizer 7). "
                + "Since 19/84 is strictly smaller than 3933/17248 and the common denominator is positive, the reverse strict inequality holds. "
                + "This contradiction proves the negation of claim. The counterexample uses a mixed state and t greater than n/2; "
                + "it does not decide monotonicity for orders at most n/2, or alter the Schatten-two result of arxiv.tex, lines 359–362.")));

    private static Formula SpinAction() => All("n", Nat, All("u", SU2,
        Equal(Typed(Local("spinAction", V("n"), V("u")), SpinMatrix(V("n"))),
            Mul(Mul(Adj(Dicke(V("n"))), Tensor(V("n"), SubtypeVal(V("u")))), Dicke(V("n"))))));

    private static Formula ReducedState()
    {
        Formula first = Word(V("t"));
        Formula last = Word(Subtract(V("n"), V("t")));
        Formula transport = new Formula.Subscript(Qualified("Equiv", "cast"), Equal(
            Parenthesized(Word(Add(V("t"), Parenthesized(Subtract(V("n"), V("t")))))),
            Parenthesized(Word(V("n")))));
        Formula e = At(Qualified("Equiv", "trans"),
            At(Qualified("Fin", "appendEquiv"), V("t"), Subtract(V("n"), V("t"))),
            transport);
        Formula symmetric = Mul(Mul(Dicke(V("n")), V("ρ")), Adj(Dicke(V("n"))));
        Formula toFun = At(Qualified("Equiv", "toFun"), V("e"));
        Formula branch = Let("e", At(Qualified("Equiv"), Product(first, last), Word(V("n"))), e,
            Mul(Mul(Adj(Dicke(V("t"))), PartialTrace(At(Qualified("Matrix", "submatrix"), symmetric, toFun, toFun))), Dicke(V("t"))));
        Formula body = Seq(Qualified("if"), Sp, LE(V("t"), V("n")), Sp,
            Qualified("then"), Sp, Parenthesized(branch), Sp, Qualified("else"), Sp, D(0));
        return All("n", Nat, All("t", Nat, All("ρ", SpinMatrix(V("n")),
            Equal(Typed(Local("reducedState", V("t"), V("ρ")), SpinMatrix(V("t"))), Parenthesized(body)))));
    }

    private static Formula Normalizer()
    {
        Formula predicate = Some("σ", SpinMatrix(V("t")),
            And(PosSemidef(V("σ")), And(Equal(Trace(V("σ")), D(1)),
                Equal(V("d"), TraceNorm(Subtract(V("σ"), At(Qualified("D5", "S3", "Quantum", "Entanglement", "Witness",
                    "WernerTesterIncompleteness", "designAverage"), Add(V("t"), D(1)))))))));
        Formula set = Seq(Left, OpenBrace, Typed(V("d"), Real), Sp, Mid, Sp, predicate, Right, CloseBrace);
        return All("t", Nat, Equal(Typed(Local("normalizer", V("t")), Real), At(Qualified("sSup"), set)));
    }

    private static Formula Anticoherence() => All("n", Nat, All("t", Nat,
        All("ρ", SpinMatrix(V("n")), Equal(Typed(Local("anticoherence", V("t"), V("ρ")), Real),
            Subtract(D(1), new Formula.Fraction(
                TraceNorm(Subtract(Local("reducedState", V("t"), V("ρ")), At(Qualified("D5", "S3", "Quantum", "Entanglement", "Witness",
                    "WernerTesterIncompleteness", "designAverage"), Add(V("t"), D(1))))),
                Local("normalizer", V("t"))))))));

    private static Formula CovariantChannel()
    {
        Formula d = Local("spinAction", V("n"), V("u"));
        Formula covariance = All("u", SU2, All("x", SpinMatrix(V("n")), Equal(
            At(V("φ"), Mul(Mul(d, V("x")), Adj(d))), Mul(Mul(d, At(V("φ"), V("x"))), Adj(d)))));
        return All("n", Nat, All("φ", MatrixMap(V("n")), IffOf(Local("IsCovariantChannel", V("φ")),
            And(At(Qualified("MatrixMap", "IsCompletelyPositive"), V("φ")),
                And(At(Qualified("MatrixMap", "IsTracePreserving"), V("φ")), covariance)))));
    }

    private static Formula Claim() => IffOf(Local("claim"), All("n", Nat, Imp(LE(D(1), V("n")),
        All("t", Nat, Imp(LE(D(1), V("t")), Imp(LE(V("t"), V("n")),
        All("φ", MatrixMap(V("n")), Imp(Local("IsCovariantChannel", V("φ")),
        All("ρ", SpinMatrix(V("n")), Imp(PosSemidef(V("ρ")), Imp(Equal(Trace(V("ρ")), D(1)),
            LE(Local("anticoherence", V("t"), V("ρ")),
                Local("anticoherence", V("t"), At(V("φ"), V("ρ")))))))))))))));

    private static Formula V(string name) => name switch
    {
        "ρ" => Rho,
        "σ" => SigmaLower,
        "φ" => Varphi,
        _ => F.Id(name)
    };
    private static Formula Qualified(params string[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(name));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Local(string name, params Formula[] args) => args.Length == 0 ? Qualified(name) : At(Qualified(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Arrow(Formula domain, Formula range) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(range));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b)));
    private static Formula Word(Formula n) => Arrow(FinOf(n), FinOf(D(2)));
    private static Formula SpinMatrix(Formula n) => At(Qualified("Matrix"), FinOf(Add(n, D(1))), FinOf(Add(n, D(1))), Complex);
    private static Formula MatrixMap(Formula n) => At(Qualified("MatrixMap"), FinOf(Add(n, D(1))), FinOf(Add(n, D(1))), Complex);
    private static Formula SU2 => At(Qualified("CoeSort", "coe"),
        At(Qualified("Matrix", "specialUnitaryGroup"), FinOf(D(2)), Complex));
    private static Formula SubtypeVal(Formula x) => At(Qualified("Subtype", "val"), x);
    private static Formula Adj(Formula x) => At(Qualified("Matrix", "conjTranspose"), x);
    private static Formula Mul(Formula x, Formula y) => Multiply(Parenthesized(x), Parenthesized(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula IffOf(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => Arrow(x, y);
    private static Formula LE(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) => Seq(Qualified("let"), Sp,
        Typed(V(name), type), Sp, Colon, Eq, Sp, value, Sp, Qualified("in"), Sp, Parenthesized(body));
    private static Formula Dicke(Formula n) => At(Qualified("dickeIsometry"), n);
    private static Formula Tensor(Formula n, Formula u) => At(Qualified("tensorOp"), At(Qualified("Function", "const"), FinOf(n), u));
    private static Formula PartialTrace(Formula x) => At(Qualified("partialTraceRight"), x);
    private static Formula Trace(Formula x) => At(Qualified("Matrix", "trace"), x);
    private static Formula PosSemidef(Formula x) => At(Qualified("Matrix", "PosSemidef"), x);
    private static Formula TraceNorm(Formula x) => At(Qualified("traceNorm"), x);
}
