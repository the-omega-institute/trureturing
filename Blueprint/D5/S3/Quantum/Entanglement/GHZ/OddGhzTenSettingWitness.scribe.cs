using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GHZ;

internal sealed class OddGhzTenSettingWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/cobuccitavakoli2024dimensionality");
    private const string Quote = "We have shown this explicitly for odd d ≤ 17 and conjecture it to hold for odd d in general.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ten-setting GHZ witness bounds fidelity and genuine multipartite Schmidt dimension in every odd local dimension.",
        H("The ten-setting GHZ witness in odd dimensions"), Blocks(
            Paragraph(Text("Fin d indexes coordinates from zero. Three-party coordinates use Fin d × (Fin d × Fin d). The symbols psi, rho and sigma denote the corresponding Lean vector and state variables. Complex.ofReal and Nat.cast display scalar embeddings; all divisions in Complex or Real are field divisions, while Nat.mod and Nat.sub retain natural remainder and truncated subtraction. Pi.single is the coordinate delta vector. Matrix.vecMulVec, Matrix.kroneckerMap, Matrix.mulVec, dotProduct and star have their usual Lean meanings. The density states are D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState; CStarMatrix.ofMatrix.symm reads their underlying matrices. Nine labelled settings are summed with multiplicity, including when d = 1.")),
            Describe.Lean(DescribeId.Create("ctw-ensemble"),
                DeclarationHandle.Create(Prefix + "Ensemble"), H("Ensemble"),
                StatementSource.FromAuthor(Disp(EnsembleFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("The dependent record has fields N, weight, nonneg, le_one, total, psi, unit and average. Page 18: “Let ρAB be a density matrix acting on CᵖA ⊗ CᑫB, where pq = n. Let Sρ = {{pi, |ψi⟩ : i = 1, 2, ..., N} : ρAB = ∑ⁿᵢ₌₁ pi|ψi⟩AB⟨ψi|, where |ψi⟩AB ∈ CᵖA ⊗ CᑫB, 0 ≤ pi ≤ 1 and ∑ᴺᵢ₌₁ pi = 1}.” The reconstruction is read over N ensemble terms and uses Euclidean unit vectors."))), DescribeRole.Definition),

            Describe.Lean(DescribeId.Create("ctw-weight-le-one"),
                DeclarationHandle.Create(Prefix + "weight_le_one_of_total"), H("A convex weight is at most one"),
                StatementSource.FromAuthor(Disp(WeightFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonnegative weight in a finite family with total one is at most one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ctw-spectral-ensemble"),
                DeclarationHandle.Create(Prefix + "spectral_ensemble_nonempty"), H("A density matrix has a finite unit-vector ensemble"),
                StatementSource.FromAuthor(Disp(SpectralFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Every positive semidefinite complex matrix on Fin p × Fin q with trace one has an Ensemble. Eigenvalues give the weights and an orthonormal eigenbasis gives the unit vectors."))), DescribeRole.Theorem),
            Paragraph(Text("Pure-state Schmidt rank uses the existing coefficient-matrix definition "),
                Ref("D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.schmidtRank"),
                Text(" on Fin m × Fin n. Printed page 3 identifies pure-state Schmidt rank with the rank of the reduced density matrix. For the three-party cuts, finProdFinEquiv flattens the other two indices to Fin (d * d); Matrix.rank_submatrix proves that this preserves coefficient-matrix rank.")),
            new DocumentBlock.DisplayFormula(Disp(SchmidtFormula())),
            Node("omega", "The exponential phase", OmegaFormula(),
                "Supplementary V, printed page 22, uses the phase ω = exp(2πi/d).", Lit()),
            Node("basisVec", "Quadratic-phase basis vectors", BasisFormula(),
                "Supplementary V, printed page 22, gives |e_l^(j)⟩ = d^(-1/2) Σ_m ω^(m(l+jm)) |m⟩. Here ω is exp(2πi/d), and the formula gives each coordinate.", Lit()),
            Node("proj", "The rank-one projector", ProjFormula(),
                "The projector |v⟩⟨v| is Matrix.vecMulVec v (star v).", Lit()),
            Node("tuples", "The nine product settings", TuplesFormula(),
                "Supplementary V, printed page 22, equation (V1), lists the nine triples in the displayed order. A List retains every label when entries coincide.", Lit()),
            Node("witness", "The ten-setting operator", WitnessFormula(),
                "Supplementary V, printed page 22: “Based on these measurements, we define the entanglement witness operator”. Equation (V2) weights the computational measurement by three and each of the nine quadratic-phase measurements by one. The modular condition is Nat.mod of the coordinate-index sum equal to zero.", Lit()),
            Node("ghz", "The three-party GHZ vector", GhzFormula(),
                "Equation (5) specializes to the normalized sum of the coordinates (i,i,i) for three parties.", Lit()),
            Node("witnessValue", "The measured expectation", ValueFormula(),
                "Supplementary V, printed page 22: “The corresponding entanglement witness quantity is therefore W_d = tr(𝒲_d ρ).” The real part of this trace is explicit.", Lit()),
            Node("ghzFidelity", "GHZ fidelity", FidelityFormula(),
                "The GHZ fidelity is the real part of the matrix expectation in the normalized three-party GHZ vector.", Lit()),
            Node("cutRank", "Schmidt rank across each cut", CutFormula(),
                "The three cuts separate party zero, one or two from the other two parties. The other two indices are flattened by finProdFinEquiv to use the frozen Schmidt-rank owner. Rank invariance under this bijection gives the displayed coefficient-matrix formula in the original index order.", Lit()),
            Node("SchmidtNumberLE", "Bounded Schmidt number", SchmidtNumberFormula(),
                "A finite convex decomposition into unit vectors whose Schmidt ranks across the chosen cut are at most r defines Schmidt number at most r.", Lit()),
            Node("GMEDecomposable", "Mixtures over the three cuts", GmeFormula(),
                "Definition 1, printed page 3: “For an arbitrary n-partite state ρ, its GME-dimension is” followed by equation (2). It minimizes over mixtures across bipartitions. Every branch has Schmidt number at most r; weights are nonnegative and sum to one.", Lit()),
            Node("gmeDim", "Genuine multipartite Schmidt dimension", DimensionFormula(),
                "Definition 1, printed page 3: “For an arbitrary n-partite state ρ, its GME-dimension is” followed by equation (2), the minimum of the admissible rank bounds. The natural infimum is attained: a spectral decomposition shows that r = d is admissible for every density state.", Lit()),
            Node("claim", "The all-odd-dimensional inequalities", IffTo(V("claim"), ClaimBody()),
                "Supplementary V, printed page 22, equations (V3)–(V5): “" + Quote + "” The universal statement includes every odd natural d, every density state, both the GME-dimension bound (V3) and the fidelity bound (V4). Oddness implies d is positive. Composite dimensions and d = 1 are included.", Lit()),
            Describe.Lean(DescribeId.Create("ctw-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Both bounds hold for every odd dimension"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Additive-character orthogonality makes the operator block diagonal in the two coordinate differences. Each nonzero difference block has at most three labelled settings at a fixed frequency: oddness makes multiplication by two cancellable, and the three signed values of any nonzero difference are distinct. Cyclic Parseval then bounds these blocks by three. The zero-difference block contributes the GHZ overlap with coefficient nine and the norm with coefficient three. A spectral decomposition extends the quadratic bound to density states. The coefficient-matrix trace bound gives fidelity at most r/d for pure states of cut rank at most r, and convexity extends it to mixtures across all three cuts. Combining these estimates proves both inequalities. Mutual unbiasedness is not used. Attainment of the non-GHZ upper bound in every odd dimension and even dimensions remain open here."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cobucci-tavakoli-2024-odd-ghz-ten-setting-witness"),
                    ResolutionKind.Proved)))));


    private static Formula Named(string name) => Seq(name.Split('_').SelectMany((part, index) =>
        index == 0 ? new Formula[] { V(part) } : new Formula[] { Underscore, Grp(V(part)) }).ToArray());
    private static Formula Instances(string carrier, Formula body, bool decidable = false) =>
        Seq(OpenBracket, Call("Fintype", V(carrier)), CloseBracket, Sp,
            decidable ? Seq(OpenBracket, Call("DecidableEq", V(carrier)), CloseBracket, Sp, body) : body);
    private static Formula EnsembleFormula()
    {
        var index = Pair(Fin(V("p")), Fin(V("q")));
        var i = V("i"); var weight = At(V("weight"), i); var psi = At(V("psi"), i);
        var fields = Seq(OpenBrace,
            V("N"), Colon, V("Nat"), Semi,
            V("weight"), Colon, Arrow(Fin(V("N")), V("Real")), Semi,
            V("nonneg"), Colon, All("i", Fin(V("N")), Leq(D(0), weight)), Semi,
            Named("le_one"), Colon, All("i", Fin(V("N")), Leq(weight, D(1))), Semi,
            V("total"), Colon, Eqn(SumOver("i", Fin(V("N")), weight), D(1)), Semi,
            V("psi"), Colon, Arrow(Fin(V("N")), Vec(index)), Semi,
            V("unit"), Colon, All("i", Fin(V("N")), Eqn(SumOver("x", index,
                new Formula.Power(Seq(Vert, Sp, At(psi, V("x")), Vert), D(2))), D(1))), Semi,
            V("average"), Colon, Eqn(SumOver("i", Fin(V("N")), C("HSMul", "hSMul", Coeff(weight),
                C("PureStateHandshake", "rankOneDensity", psi))), V("rho")), CloseBrace);
        return All("p", V("Nat"), All("q", V("Nat"), All("rho", Call("Matrix", index, index, V("Complex")),
            Eqn(Call("Ensemble", V("rho")), fields))));
    }

    private static Formula WeightFormula() => All("iota", V("Type"), Instances("iota",
        All("weight", Arrow(V("iota"), V("Real")),
            Imp(All("j", V("iota"), Leq(D(0), At(V("weight"), V("j")))),
                Imp(Eqn(SumOver("j", V("iota"), At(V("weight"), V("j"))), D(1)),
                    All("i", V("iota"), Leq(At(V("weight"), V("i")), D(1)))))), true));
    private static Formula SpectralFormula()
    {
        var index = Pair(Fin(V("p")), Fin(V("q")));
        return All("p", V("Nat"), All("q", V("Nat"), All("rho", Call("Matrix", index, index, V("Complex")),
            Imp(C("Matrix", "PosSemidef", V("rho")), Imp(Eqn(C("Matrix", "trace", V("rho")), D(1)),
                Call("Nonempty", Call("Ensemble", V("rho"))))))));
    }

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(DescribeId.Create("ctw-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(V(name), args);
    private static Formula C(string owner, string name, params Formula[] args) => At(Q(owner, name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Times, Sp, b));
    private static Formula Tuple(Formula a, Formula b, Formula c) => Parenthesized(Seq(a, Comma, b, Comma, c));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Index() => Pair(Fin(V("d")), Pair(Fin(V("d")), Fin(V("d"))));
    private static Formula Vec(Formula index) => Arrow(index, V("Complex"));
    private static Formula State() => Call("DensityState", Index());
    private static Formula Dim(Formula body) => All("d", V("Nat"), body);
    private static Formula StateBind(Formula body) => Dim(All("rho", State(), body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, V(name), Colon, type, Comma, Sp, body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Grp(Seq(V(name), Colon, type))), Parenthesized(body));
    private static Formula Fst(Formula x) => C("Prod", "fst", x);
    private static Formula Snd(Formula x) => C("Prod", "snd", x);
    private static Formula Coeff(Formula x) => C("Complex", "ofReal", x);
    private static Formula RealD() => C("Nat", "cast", V("d"));
    private static Formula ComplexD() => C("Nat", "cast", V("d"));
    private static Formula Coefficient() => new Formula.Fraction(D(1), Coeff(C("Real", "sqrt", RealD())));
    private static Formula Projection(Formula v) => C("Matrix", "vecMulVec", v, Call("star", v));
    private static Formula Raw(Formula rho) => At(Seq(Q("CStarMatrix", "ofMatrix"), Dot, V("symm")),
        Seq(rho, Dot, D(1)));
    private static Formula Tensor(Formula a, Formula b) => C("Matrix", "kroneckerMap",
        LambdaOf("x", V("Complex"), LambdaOf("y", V("Complex"), Multiply(V("x"), V("y")))), a, b);
    private static Formula DotProduct(Formula a, Formula b) => Call("dotProduct", a, b);
    private static Formula Ket(Formula i) => C("Pi", "single", i, D(1));

    private static Formula SchmidtFormula() => All("m", V("Nat"), All("n", V("Nat"),
        All("v", Vec(Pair(Fin(V("m")), Fin(V("n")))), Eqn(Call("schmidtRank", V("v")),
            C("Matrix", "rank", C("Matrix", "of", LambdaOf("i", Fin(V("m")),
                LambdaOf("j", Fin(V("n")), At(V("v"), Parenthesized(Seq(V("i"), Comma, V("j"))))))))))));
    private static Formula OmegaFormula() => Dim(Eqn(Call("omega", V("d")),
        C("Complex", "exp", new Formula.Fraction(
            Multiply(Multiply(D(2), Coeff(Q("Real", "pi"))), Q("Complex", "I")), ComplexD()))));
    private static Formula ProjFormula() => Dim(All("v", Vec(Fin(V("d"))),
        Eqn(Call("proj", V("v")), Projection(V("v")))));
    private static Formula BasisFormula()
    {
        var m = C("Fin", "val", V("m"));
        var phase = Call("omega", V("d"));
        return Dim(All("j", V("Nat"), All("l", V("Nat"), Eqn(Call("basisVec", V("d"), V("j"), V("l")),
            LambdaOf("m", Fin(V("d")), Multiply(Coefficient(), new Formula.Power(phase,
                Multiply(m, Add(V("l"), Multiply(V("j"), m))))))))));
    }
    private static Formula TuplesFormula()
    {
        var d = V("d"); var a = C("Nat", "sub", d, D(1)); var b = C("Nat", "sub", d, D(2));
        return Dim(Eqn(Call("tuples", d), Seq(OpenBracket,
            Tuple(D(0), D(0), D(0)), Comma, Tuple(D(1), D(1), b), Comma, Tuple(a, a, D(2)), Comma,
            Tuple(D(0), D(1), a), Comma, Tuple(D(1), D(0), a), Comma, Tuple(D(0), a, D(1)), Comma,
            Tuple(D(1), a, D(0)), Comma, Tuple(a, D(0), D(1)), Comma, Tuple(a, D(1), D(0)), CloseBracket)));
    }
    private static Formula WitnessFormula()
    {
        var l = V("l"); var j = V("j"); var d = V("d");
        var computational = SumOver("l", Fin(d), Tensor(Call("proj", Ket(l)),
            Tensor(Call("proj", Ket(l)), Call("proj", Ket(l)))));
        Formula Basis(Formula index, Formula label) => Call("proj", Call("basisVec", d, index,
            C("Fin", "val", label)));
        var term = Tensor(Basis(Fst(j), Fst(l)),
            Tensor(Basis(Fst(Snd(j)), Fst(Snd(l))), Basis(Snd(Snd(j)), Snd(Snd(l)))));
        var constraint = Eqn(C("Nat", "mod", Add(Add(C("Fin", "val", Fst(l)),
            C("Fin", "val", Fst(Snd(l)))), C("Fin", "val", Snd(Snd(l)))), d), D(0));
        var filtered = C("Finset", "filter", LambdaOf("l", Index(), constraint),
            Seq(Q("Finset", "univ"), Colon, Call("Finset", Index())));
        var localSum = C("Finset", "sum", filtered, LambdaOf("l", Index(), term));
        var tripleNat = Pair(V("Nat"), Pair(V("Nat"), V("Nat")));
        var settings = C("List", "sum", C("List", "map", LambdaOf("j", tripleNat, localSum), Call("tuples", d)));
        return Dim(Eqn(Call("witness", d), Add(C("HSMul", "hSMul", C("Nat", "cast", D(3)), computational), settings)));
    }
    private static Formula GhzFormula() => Dim(Eqn(Call("ghz", V("d")),
        C("HSMul", "hSMul", Coefficient(), SumOver("i", Fin(V("d")),
            Seq(Ket(Tuple(V("i"), V("i"), V("i"))), Colon, Vec(Index()))))));
    private static Formula ValueFormula() => StateBind(Eqn(Call("witnessValue", V("d"), V("rho")),
        C("Complex", "re", C("Matrix", "trace", Multiply(Call("witness", V("d")), Raw(V("rho")))))));
    private static Formula FidelityFormula() => StateBind(Eqn(Call("ghzFidelity", V("d"), V("rho")),
        C("Complex", "re", DotProduct(Call("star", Call("ghz", V("d"))),
            C("Matrix", "mulVec", Raw(V("rho")), Call("ghz", V("d")))))));
    private static Formula CutFormula()
    {
        var x = V("i"); var y = Fst(V("j")); var z = Snd(V("j"));
        Formula Rank(Formula a, Formula b, Formula c) => C("Matrix", "rank", C("Matrix", "of",
            LambdaOf("i", Fin(V("d")), LambdaOf("j", Pair(Fin(V("d")), Fin(V("d"))),
                At(V("psi"), Tuple(a, b, c))))));
        return Dim(All("k", Fin(D(3)), All("psi", Vec(Index()), Eqn(Call("cutRank", V("k"), V("psi")),
            Seq(V("if"), Sp, Eqn(C("Fin", "val", V("k")), D(0)), Sp, V("then"), Sp, Rank(x, y, z),
                Sp, V("else"), Sp, V("if"), Sp, Eqn(C("Fin", "val", V("k")), D(1)), Sp, V("then"),
                Sp, Rank(y, x, z), Sp, V("else"), Sp, Rank(y, z, x))))));
    }
    private static Formula SchmidtNumberFormula()
    {
        var i = V("i"); var psi = At(V("psi"), i); var p = At(V("p"), i);
        var rhs = Ex("m", V("Nat"), Ex("p", Arrow(Fin(V("m")), V("Real")),
            Ex("psi", Arrow(Fin(V("m")), Vec(Index())),
                And(All("i", Fin(V("m")), Leq(D(0), p)),
                And(Eqn(SumOver("i", Fin(V("m")), p), D(1)),
                And(All("i", Fin(V("m")), Eqn(DotProduct(Call("star", psi), psi), D(1))),
                And(All("i", Fin(V("m")), Leq(Call("cutRank", V("k"), psi), V("r"))),
                    Eqn(Raw(V("sigma")), SumOver("i", Fin(V("m")), C("HSMul", "hSMul", Coeff(p), Projection(psi)))))))))));
        return Dim(All("k", Fin(D(3)), All("r", V("Nat"), All("sigma", State(),
            IffTo(Call("SchmidtNumberLE", V("k"), V("r"), V("sigma")), rhs)))));
    }
    private static Formula GmeFormula()
    {
        var k = V("k"); var weight = At(V("q"), k); var sigma = At(V("sigma"), k);
        var rhs = Ex("q", Arrow(Fin(D(3)), V("Real")), Ex("sigma", Arrow(Fin(D(3)), State()),
            And(All("k", Fin(D(3)), Leq(D(0), weight)),
            And(Eqn(SumOver("k", Fin(D(3)), weight), D(1)),
            And(All("k", Fin(D(3)), Call("SchmidtNumberLE", k, V("r"), sigma)),
                Eqn(Raw(V("rho")), SumOver("k", Fin(D(3)), C("HSMul", "hSMul", Coeff(weight), Raw(sigma)))))))));
        return StateBind(All("r", V("Nat"), IffTo(Call("GMEDecomposable", V("r"), V("rho")), rhs)));
    }
    private static Formula DimensionFormula() => StateBind(Eqn(Call("gmeDim", V("rho")),
        Call("sInf", Seq(OpenBrace, V("r"), Colon, V("Nat"), Bar,
            Call("GMEDecomposable", V("r"), V("rho")), CloseBrace))));
    private static Formula ClaimBody() => Dim(Imp(Call("Odd", V("d")), All("rho", State(),
        And(Leq(Call("witnessValue", V("d"), V("rho")), Add(D(3), new Formula.Fraction(
                Multiply(D(9), C("Nat", "cast", Call("gmeDim", V("rho")))), RealD()))),
            Leq(new Formula.Fraction(Subtract(Call("witnessValue", V("d"), V("rho")), D(3)), D(9)),
                Call("ghzFidelity", V("d"), V("rho")))))));
}
