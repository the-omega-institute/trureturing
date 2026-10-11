using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CCZMagicCapacityThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/CCZMagicCapacityThreshold.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/wei2024magicnoise");
    private const string NormalFormQuote = "Printed page 11, Appendix D, Eq. (D2): \"Any pure n-qubit stabilizer state has the form |𝒦,q,𝐛⟩ := (1/√|𝒦|) ∑_{x∈𝒦} i^{𝐛·x}(−1)^{q(x)}|x⟩, where 𝒦 ⊂ 𝔽₂ⁿ is an affine subspace, 𝐛 ∈ 𝔽₂ⁿ, q is a quadratic form, and i = √−1.\" Computational labels are functions Fin n -> Bool; affine coordinates are functions Fin n -> ZMod 2. The exponent of Complex.I sums integer lifts before exponentiation. Upper-triangular coefficients include diagonal terms, which represent linear monomials over ZMod 2.";
    private const string NoiseQuote = "Printed page 2: \"As a standard noise model, we primarily consider the independent depolarizing noise 𝓔_λ^{⊗n} acting on the n-body quantum system, which leaves the qubits it acts on unchanged with probability 1−λ, and replaces them with 𝕀₂/2 with probability λ.\" The trace factor extends the channel to all matrices. Coordinates 0, 1 and 2 form A; coordinates 3, 4 and 5 form its reference B.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The noisy CCZ gate preserves magic with a reference at depolarizing strength 1/2.",
        H("A reference preserves CCZ magic beyond one third"),
        Blocks(
            Node("qUpper", "Binary quadratic polynomials", QuadraticFormula(), NormalFormQuote),
            Node("IsQuad", "Upper-triangular quadratic representation", IsQuadFormula(), NormalFormQuote),
            Node("stabVec", "Stabilizer normal-form amplitudes", StabilizerVectorFormula(), NormalFormQuote + " The affine support has cardinality (K : Set (Fin n -> ZMod 2)).toFinset.card. Its zero-support expression is defined, while pure stabilizer membership requires nonempty support."),
            Node("IsPureStab", "Pure stabilizer density matrices", PureFormula(), NormalFormQuote + " Density matrices are Matrix.vecMulVec v (star v); a nonempty affine support and a quadratic phase are required."),
            Node("STAB", "Stabilizer mixtures", MixtureFormula(), "Printed page 2, Section II: \"Let STABₙ denote the set of all n-qubit stabilizer states, namely the convex hull of all pure stabilizer states.\" The convex hull is over the real scalar field."),
            Node("depol", "Single-qubit depolarizing noise", DepolarizingFormula(), NoiseQuote + " The Lean body is the frozen owner's D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized at d = 2, reindexed along finTwoEquiv; the private lemma D5.S3.Quantum.Information.CCZMagicCapacityThreshold.depol_formula proves that this body agrees with the displayed source expression."),
            Node("depolAt", "Depolarization at one coordinate", DepolarizingAtFormula(), NoiseQuote + " For each fixed pair of outside labels, apply depol to the two-by-two block obtained with Function.update."),
            Node("depolA", "Noise on the three system qubits", DepolarizingAFormula(), NoiseQuote),
            Node("CCZ", "The controlled-controlled-Z gate", GateFormula(), "Printed page 2: \"Let Cⁿ⁻¹Z = diag(1, · · · , 1, −1) denote the multi-controlled-Z gate on n-qubits, with C⁰Z = Z.\" At n = 3, the computational-basis diagonal is -1 at 111 and 1 at every other label; Bool.and is the Boolean conjunction used by the diagonal entries."),
            Node("CCZA", "CCZ with an untouched reference", GateAFormula(), "CCZA is the diagonal six-qubit matrix obtained from CCZ on the first three bits. Fin.castAdd 3 selects A; the last three coordinates form B."),
            Node("chan", "Gate followed by local noise", ChannelFormula(), NoiseQuote + " CCZ is real and diagonal, so the displayed two-sided multiplication is its unitary conjugation. The reference is untouched."),
            Node("claim", "The conjectured magic-capacity threshold", ClaimFormula(), "Printed page 6, Section VII: \"We conjecture that the magic capacity threshold for CCZ under local depolarizing noise is 1/3.\" Printed page 3: \"Define the magic capacity [31] of the Cⁿ⁻¹Z gate as 𝒞(Cⁿ⁻¹Z)=max_{|s⟩}𝓡(Cⁿ⁻¹Z⊗𝕀_{2ⁿ}|s⟩), where the maximum is taken over all 2n-qubit pure stabilizer states |s⟩.\" Page 2 gives faithfulness: RoM equals 1 exactly on STAB. The first conjunct encodes capacity one for every noise strength in [1/3,1]; the second encodes capacity greater than one below 1/3. Inputs range over pure stabilizer density matrices on six qubits. Only A is noisy, in the noise-after-gate order."),
            Describe.Lean(DescribeId.Create("ccz-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The one-third capacity conjecture is false"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At lambda = 1/2, use the pure stabilizer input Omega = 8^(-1/2) sum_x |x,x>. Restricting any stabilizer amplitude to the diagonal produces either zero or a scalar multiple of a three-qubit stabilizer normal form. The binary phase vector becomes b_A + b_B, and the quadratic phase acquires the carry term sum_i b_A(i)b_B(i)x_i^2. The squared overlap with CCZ|+++> is at most 9/16: proper affine supports have at most four points, and the full-support bound follows from the exact finite phase sum. Consequently the separating matrix has nonnegative trace pairing with every stabilizer mixture. Its trace pairing with chan (1/2) applied to the Omega density matrix is exactly -7/1024, contradicting the first conjunct of claim. This proves the refutation at one half; it does not determine the exact threshold."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wei-liu-2024-ccz-magic-capacity-threshold"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("ccz-" + declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Ration(byte a, byte b) => new Formula.Fraction(D(a), D(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula BinaryType() => Call("ZMod", D(2));
    private static Formula Labels(Formula n) => Parenthesized(Arrow(Call("Fin", n), F.Id("Bool")));
    private static Formula Coordinates(Formula n) => Parenthesized(Arrow(Call("Fin", n), BinaryType()));
    private static Formula MatrixType(Formula n) => Call("Matrix", Labels(n), Labels(n), ComplexType());
    private static Formula SupportType(Formula n) => Call("AffineSubspace", BinaryType(), Coordinates(n));
    private static Formula PhaseType(Formula n) => Parenthesized(Arrow(Coordinates(n), BinaryType()));
    private static Formula Coefficients(Formula n) => Parenthesized(Arrow(Call("Fin", n), Arrow(Call("Fin", n), BinaryType())));
    private static Formula Lambda(string name, Formula type, Formula value) => Parenthesized(Seq(F.Id("fun"), Sp, F.Id(name), Sp, Colon, Sp, type, Sp, Mapsto, Sp, value));
    private static Formula If(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(F.Id("if"), Sp, condition, Sp, F.Id("then"), Sp, yes, Sp, F.Id("else"), Sp, no));
    private static Formula SumOver(string name, Formula n, Formula value) => Seq(Sum, Underscore, Grp(F.Id(name), Colon, Call("Fin", n)), Sp, value);
    private static Formula Value(Formula x) => Call("val", x);
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, type));
    private static Formula BitCoordinates(Formula n, Formula x) => Lambda("i", Call("Fin", n), If(App(x, F.Id("i")), Cast(D(1), BinaryType()), D(0)));
    private static Formula Slice(Formula x) => Lambda("i", Call("Fin", D(3)), App(x, App(Q("Fin", "castAdd"), D(3), F.Id("i"))));
    private static Formula BinaryAll(Formula x) => App(Q("Bool", "and"), App(Q("Bool", "and"), App(x, D(0)), App(x, D(1))), App(x, D(2)));

    private static Formula QuadraticFormula()
    {
        Formula n = F.Id("n"), c = F.Id("c"), x = F.Id("x"), i = F.Id("i"), j = F.Id("j");
        Formula term = If(new Formula.Relation(i, FormulaRelationOperator.LessThanOrEqual, j), Multiply(Multiply(App(c, i, j), App(x, i)), App(x, j)), D(0));
        return All("n", NatType(), All("c", Coefficients(n), All("x", Coordinates(n), Equal(Call("qUpper", c, x), SumOver("i", n, SumOver("j", n, term))))));
    }

    private static Formula IsQuadFormula()
    {
        Formula n = F.Id("n"), q = F.Id("q"), c = F.Id("c");
        return All("n", NatType(), All("q", PhaseType(n), Equivalent(Call("IsQuad", q), Some("c", Coefficients(n), Equal(q, Call("qUpper", c))))));
    }

    private static Formula StabilizerVectorFormula()
    {
        Formula n = F.Id("n"), k = F.Id("K"), q = F.Id("q"), b = F.Id("b"), x = F.Id("x"), u = F.Id("u"), i = F.Id("i");
        Formula cardinality = Seq(Parenthesized(Seq(k, Colon, Call("Set", Coordinates(n)))), Dot, F.Id("toFinset"), Dot, F.Id("card"));
        Formula root = App(Q("Complex", "ofReal"), App(Q("Real", "sqrt"), Cast(cardinality, RealType())));
        Formula phase = Multiply(Multiply(Power(root, new Formula.Negate(D(1))),
            Power(Q("Complex", "I"), SumOver("i", n, Multiply(Value(App(b, i)), Value(App(u, i)))))),
            Power(Parenthesized(new Formula.Negate(D(1))), Value(App(q, u))));
        Formula body = Seq(F.Id("let"), Sp, u, Colon, Coordinates(n), Sp, Eq, Sp, BitCoordinates(n, x), Semi, Sp,
            Equal(Call("stabVec", n, k, q, b, x), If(Member(u, k), phase, D(0))));
        return All("n", NatType(), All("K", SupportType(n), All("q", PhaseType(n), All("b", Coordinates(n), All("x", Labels(n), body)))));
    }

    private static Formula PureFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho"), k = F.Id("K"), q = F.Id("q"), b = F.Id("b");
        Formula vector = Call("stabVec", n, k, q, b);
        Formula nonempty = Seq(Parenthesized(Seq(k, Colon, Call("Set", Coordinates(n)))), Dot, F.Id("Nonempty"));
        Formula conditions = Both(nonempty, Both(Call("IsQuad", q), Equal(rho, App(Q("Matrix", "vecMulVec"), vector, Call("star", vector)))));
        return All("n", NatType(), All("rho", MatrixType(n), Equivalent(Call("IsPureStab", n, rho), Some("K", SupportType(n), Some("q", PhaseType(n), Some("b", Coordinates(n), conditions))))));
    }

    private static Formula MixtureFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho");
        Formula pure = Seq(OpenBrace, rho, Colon, MatrixType(n), Sp, Mid, Sp, Call("IsPureStab", n, rho), CloseBrace);
        return All("n", NatType(), Equal(Call("STAB", n), Call("convexHull", RealType(), pure)));
    }

    private static Formula DepolarizingFormula()
    {
        Formula lam = F.Id("lam"), rho = F.Id("rho");
        Formula matrix = Call("Matrix", F.Id("Bool"), F.Id("Bool"), ComplexType());
        Formula source = Add(Multiply(Subtract(D(1), lam), rho),
            Multiply(new Formula.Fraction(lam, D(2)), Multiply(App(Q("Matrix", "trace"), rho), Q("Matrix", "one"))));
        return All("lam", RealType(), All("rho", matrix, Equal(Call("depol", lam, rho), source)));
    }

    private static Formula DepolarizingAtFormula()
    {
        Formula lam = F.Id("lam"), j = F.Id("j"), rho = F.Id("rho"), x = F.Id("x"), y = F.Id("y"), u = F.Id("u"), v = F.Id("v");
        Formula block = Lambda("u", F.Id("Bool"), Lambda("v", F.Id("Bool"), App(rho, App(Q("Function", "update"), x, j, u), App(Q("Function", "update"), y, j, v))));
        return All("lam", RealType(), All("j", Call("Fin", D(6)), All("rho", MatrixType(D(6)), All("x", Labels(D(6)), All("y", Labels(D(6)),
            Equal(Call("depolAt", lam, j, rho, x, y), Call("depol", lam, block, App(x, j), App(y, j))))))));
    }

    private static Formula DepolarizingAFormula()
    {
        Formula lam = F.Id("lam"), rho = F.Id("rho");
        return All("lam", RealType(), All("rho", MatrixType(D(6)), Equal(Call("depolA", lam, rho),
            Call("depolAt", lam, D(2), Call("depolAt", lam, D(1), Call("depolAt", lam, D(0), rho))))));
    }

    private static Formula GateFormula()
    {
        Formula x = F.Id("x");
        return Equal(F.Id("CCZ"), App(Q("Matrix", "diagonal"), Lambda("x", Labels(D(3)), If(BinaryAll(x), new Formula.Negate(D(1)), D(1)))));
    }

    private static Formula GateAFormula()
    {
        Formula x = F.Id("x");
        return Equal(F.Id("CCZA"), App(Q("Matrix", "diagonal"), Lambda("x", Labels(D(6)), Call("CCZ", Slice(x), Slice(x)))));
    }

    private static Formula ChannelFormula()
    {
        Formula lam = F.Id("lam"), rho = F.Id("rho"), gate = F.Id("CCZA");
        return All("lam", RealType(), All("rho", MatrixType(D(6)), Equal(Call("chan", lam, rho), Call("depolA", lam, Multiply(Multiply(gate, rho), gate)))));
    }

    private static Formula ClaimFormula()
    {
        Formula lam = F.Id("lam"), rho = F.Id("rho");
        Formula stable = Member(Call("chan", lam, rho), Call("STAB", D(6)));
        Formula high = All("lam", RealType(), ImpliesTo(Member(lam, App(Q("Set", "Icc"), Ration(1, 3), D(1))),
            All("rho", MatrixType(D(6)), ImpliesTo(Call("IsPureStab", D(6), rho), stable))));
        Formula low = All("lam", RealType(), ImpliesTo(Member(lam, App(Q("Set", "Ico"), D(0), Ration(1, 3))),
            Some("rho", MatrixType(D(6)), Both(Call("IsPureStab", D(6), rho), new Formula.Not(stable)))));
        return Equivalent(F.Id("claim"), Both(high, low));
    }
}
