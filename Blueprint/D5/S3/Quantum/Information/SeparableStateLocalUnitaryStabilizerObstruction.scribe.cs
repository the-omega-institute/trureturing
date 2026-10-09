using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SeparableStateLocalUnitaryStabilizerObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/qian2025nonlocalnonstabilizerness");
    private const string Conjecture = "Appendix F, PDF p. 8, verbatim: “However, we are unaware of any proof guaranteeing that every separable multi-qubit state can be transformed into a state belonging to STAB using only local unitary transformations, and we conjecture that this is not the case.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-two mixture of two nonorthogonal product states remains outside the full convex stabilizer hull under every local unitary.",
        H("Separable states outside every local-unitary stabilizer frame"),
        Blocks(
            Node("unitVector", "Normalized pure vectors", UnitFormula(),
                "A pure vector has squared norm one. star is componentwise complex conjugation and dotProduct sums over the finite index type n. The Fintype argument is an instance, rather than a named mathematical variable.", DescribeRole.Definition),
            Node("IsHermitianPauli", "Signed Hermitian two-qubit Paulis", PauliFormula(),
                "The Pauli labels and literal matrices are those of StabilizerPairLocalUnitaryInequivalence: I, X, Y = i X Z, and Z. Only the real signs plus and minus are allowed, so these operators are Hermitian. The Kronecker product acts on the same two computational indices.", DescribeRole.Definition),
            Node("PureStabilizer", "Two independent commuting generators", PureFormula(),
                "A two-qubit pure stabilizer vector is normalized and fixed by two commuting signed Hermitian Pauli matrices. Each generator differs from both signs of the identity, and the second differs from both signs of the first. These conditions express two independent nontrivial stabilizer generators.", DescribeRole.Definition),
            Node("STAB", "The full convex stabilizer hull", StabFormula(),
                "Appendix F, PDF p. 8, preceding equation (F2), verbatim: “while STAB is defined as the convex hull of pure stabilizer states:” The equation is STAB := {ρ | ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|}, followed by “where ψᵢ are pure stabilizer states.” convexHull over the real numbers encodes all finite probability mixtures. PureStateHandshake.rankOneDensity is literally Matrix.vecMulVec(psi,star(psi)). STAB includes mixtures drawn from different stabilizer bases.", DescribeRole.Definition),
            Node("localMatrix", "The common product unitary", LocalMatrixFormula(),
                "The two matrices belong to Matrix.unitaryGroup(Fin(2),C). val exposes their matrices, and their Kronecker product is the unitary on the joint system.", DescribeRole.Definition),
            Node("localAction", "Local-unitary conjugation", ActionFormula(),
                "The same pair of local unitaries acts on the entire density matrix. conjTranspose is the complex matrix adjoint.", DescribeRole.Definition),
            Node("ProductPureProjectors", "Pure product-state projectors", ProductFormula(),
                "Both local vectors are normalized. FiniteLocalLatitudeGeometry.productVector supplies their literal product amplitude a(i) b(j), which is projected by the existing rankOneDensity construction, giving the tensor product of the two local rank-one density matrices.", DescribeRole.Definition),
            Node("Separable", "Separable mixed states", SeparableFormula(),
                "Appendix F, PDF p. 8, preceding equation (F1), verbatim: “A separable state is defined as the convex hull of pure product states [1]:” The real convex hull allows every finite ensemble of normalized product-state projectors.", DescribeRole.Definition),
            Node("claim", "Qian–Wang's separable-state conjecture", ClaimFormula(),
                Conjecture + " The existential two-qubit density matrix rho is positive semidefinite with trace one, as expressed by StructuredNegativityCoincidenceRefutation.IsDensity. Its separability is the literal convex-product-ensemble condition. The universal quantifier ranges independently over all pairs of single-qubit unitaries. A two-qubit example proves the source's existential multi-qubit assertion.", DescribeRole.Definition),
            Node("marginal_amplitude", "The reduced projector is an amplitude Gram matrix",
                Disp(All("psi", Vector, EqTo(Call("partialTraceRight", RankOne(F.Id("psi"))),
                    Mul(Call("Matrix.of", Call("Function.curry", F.Id("psi"))),
                        Call("conjTranspose", Call("Matrix.of", Call("Function.curry", F.Id("psi")))))))),
                "For a two-qubit vector, curry arranges its amplitudes into a two-by-two matrix. Tracing the right subsystem of its rank-one projector gives that matrix times its adjoint.", DescribeRole.Theorem, true),
            Node("ensemble_kernel", "Zero quadratic form constrains every positive-weight vector", EnsembleKernelFormula(),
                "Let psi be a finite family of complex vectors with nonnegative real weights w. If the quadratic form of their weighted rank-one projector sum vanishes at z, then every positive-weight vector is orthogonal to z. Positivity of the weighted squared overlaps prevents cancellation.", DescribeRole.Theorem, true),
            Node("result", "An infinite family proves the conjecture", Disp(Named("claim")),
                "For every real p,c,s with 0 < p < 1, c > 0, s > 0, c² + s² = 1 and c² ≠ 1/2, put b = (c,s) and rho = p |00⟩⟨00| + (1-p) |bb⟩⟨bb|. This is a density matrix and an explicit convex mixture of product pure states, yet no local-unitary conjugate belongs to STAB. Choose p = 1/2, c = 3/5 and s = 4/5 for the existential conclusion. Every positive-weight vector in any pulled-back stabilizer ensemble lies in span{u,v}, where u = |00⟩ and v = |bb⟩. Its only product rays are u and v; its only maximally entangled ray has coefficients alpha = -beta, namely (v-u)/(sqrt(2)s) after normalization. Stabilizer classification and positivity eliminate that entangled ray from the ensemble, forcing both product rays to occur. Their common local unitary preserves the single-qubit squared overlap c², whereas Pauli eigenprojectors have overlap spectrum {0,1/2,1}. The stated parameter conditions exclude all three values. This argument uses product-vector and maximal-entanglement invariance under local unitaries; the Pauli restriction enters after stabilizer classification.", DescribeRole.Theorem, true,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("qian-wang-2025-separable-states-stab-local-unitaries"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool derived = false, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("qw-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name)
    {
        string[] words = name.Split('.');
        Formula[] items = new Formula[words.Length * 2 - 1];
        for (int i = 0; i < words.Length; i++)
        {
            items[2 * i] = F.Id(words[i]);
            if (i + 1 < words.Length) items[2 * i + 1] = Dot;
        }
        return Seq(Operatorname, Grp(items));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula InTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(params Formula[] xs)
    {
        Formula result = xs[^1];
        for (int i = xs.Length - 2; i >= 0; i--) result = Logic(xs[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula IffTo(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula OrTo(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Neg(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula Kron(Formula a, Formula b) => Call("Matrix.kronecker", a, b);
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula SetOf(string name, Formula type, Formula predicate) => Seq(OpenBrace, F.Id(name), Colon, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinTwo => Call("Fin", D(2));
    private static Formula Joint => Product(FinTwo, FinTwo);
    private static Formula Vector => Arrow(Joint, Complexes);
    private static Formula LocalVector => Arrow(FinTwo, Complexes);
    private static Formula Mat => Call("Matrix", Joint, Joint, Complexes);
    private static Formula Unitary => Call("Matrix.unitaryGroup", FinTwo, Complexes);
    private static Formula Pauli => Named("Pauli");
    private static Formula PauliMatrix(Formula p) => Call("pauliMatrix", p);
    private static Formula RankOne(Formula p) => Call("rankOneDensity", p);
    private static Formula Unit(Formula p) => Call("unitVector", p);

    private static Formula UnitFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x");
        return Disp(All("n", Named("Type"), Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
            All("x", Arrow(n, Complexes), IffTo(Unit(x), EqTo(Call("dotProduct", Call("star", x), x), D(1)))))));
    }
    private static Formula PauliFormula()
    {
        Formula p = F.Id("P"), a = F.Id("a"), b = F.Id("b");
        Formula product = Kron(PauliMatrix(a), PauliMatrix(b));
        return Disp(All("P", Mat, IffTo(Call("IsHermitianPauli", p), Some("a", Pauli, Some("b", Pauli,
            OrTo(EqTo(p, product), EqTo(p, Neg(product))))))));
    }
    private static Formula PureFormula()
    {
        Formula psi = F.Id("psi"), p = F.Id("P"), q = F.Id("Q");
        Formula fixedBy(Formula a) => EqTo(Call("Matrix.mulVec", a, psi), psi);
        Formula generators = And(Call("IsHermitianPauli", p), Call("IsHermitianPauli", q),
            NeTo(p, D(1)), NeTo(p, Neg(D(1))), NeTo(q, D(1)), NeTo(q, Neg(D(1))),
            NeTo(q, p), NeTo(q, Neg(p)), EqTo(Mul(p, q), Mul(q, p)), fixedBy(p), fixedBy(q));
        return Disp(All("psi", Vector, IffTo(Call("PureStabilizer", psi),
            And(Unit(psi), Some("P", Mat, Some("Q", Mat, generators))))));
    }
    private static Formula StabFormula()
    {
        Formula a = F.Id("A"), psi = F.Id("psi");
        Formula set = SetOf("A", Mat, Some("psi", Vector, And(Call("PureStabilizer", psi), EqTo(a, RankOne(psi)))));
        return Disp(EqTo(Named("STAB"), Call("convexHull", Reals, set)));
    }
    private static Formula LocalMatrixFormula()
    {
        Formula ua = F.Id("UA"), ub = F.Id("UB");
        return Disp(All("UA", Unitary, All("UB", Unitary, EqTo(Call("localMatrix", ua, ub), Kron(Call("val", ua), Call("val", ub))))));
    }
    private static Formula ActionFormula()
    {
        Formula ua = F.Id("UA"), ub = F.Id("UB"), rho = F.Id("rho"), matrix = Call("localMatrix", ua, ub);
        return Disp(All("UA", Unitary, All("UB", Unitary, All("rho", Mat,
            EqTo(Call("localAction", ua, ub, rho), Mul(Mul(matrix, rho), Call("conjTranspose", matrix)))))));
    }
    private static Formula ProductFormula()
    {
        Formula a = F.Id("A"), x = F.Id("a"), y = F.Id("b");
        Formula set = SetOf("A", Mat, Some("a", LocalVector, Some("b", LocalVector,
            And(Unit(x), Unit(y), EqTo(a, RankOne(Call("productVector", x, y)))))));
        return Disp(EqTo(Named("ProductPureProjectors"), set));
    }
    private static Formula SeparableFormula()
    {
        Formula rho = F.Id("rho");
        return Disp(All("rho", Mat, IffTo(Call("Separable", rho), InTo(rho, Call("convexHull", Reals, Named("ProductPureProjectors"))))));
    }
    private static Formula EnsembleKernelFormula()
    {
        Formula n = F.Id("n"), index = F.Id("iota"), psi = F.Id("psi"), w = F.Id("w"), z = F.Id("z"), i = F.Id("i");
        Formula family = Seq(Sum, Underscore, Grp(i, InMacro, Sp, index), Sp,
            Parenthesized(Seq(Call("w", i), Cdot, Sp, RankOne(Call("psi", i)))));
        Formula dot(Formula x) => Call("dotProduct", Call("star", z), x);
        Formula assumptions = And(All("i", index, Seq(D(0), Le, Sp, Call("w", i))),
            EqTo(dot(Call("Matrix.mulVec", family, z)), D(0)));
        Formula conclusion = All("i", index, Seq(D(0), Lt, Call("w", i), Longrightarrow, Sp,
            EqTo(dot(Call("psi", i)), D(0))));
        return Disp(All("n", Named("Type"), All("iota", Named("Type"),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp, OpenBracket, Call("Fintype", index), CloseBracket, Sp,
                All("psi", Arrow(index, Arrow(n, Complexes)), All("w", Arrow(index, Reals),
                    All("z", Arrow(n, Complexes), Seq(assumptions, Longrightarrow, Sp, conclusion))))))));
    }
    private static Formula ClaimFormula()
    {
        Formula rho = F.Id("rho"), ua = F.Id("UA"), ub = F.Id("UB");
        Formula excluded = new Formula.Not(Parenthesized(InTo(Call("localAction", ua, ub, rho), Named("STAB"))));
        return Disp(IffTo(Named("claim"), Some("rho", Mat,
            And(Call("IsDensity", rho), Call("Separable", rho),
                All("UA", Unitary, All("UB", Unitary, excluded))))));
    }
}
