using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class KickedIsingNegativityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/pathak2026mixedstate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pathak's generic-state negativity identity fails on a four-site kicked Ising chain.",
        H("A generic-state counterexample in the kicked Ising chain"),
        Blocks(
            Node("hIsing", "Ising Hamiltonian", IsingFormula(),
                "Equation (1), p. 1, defines H_I = J ∑ᵢ σᶻᵢσᶻᵢ₊₁ + ∑ᵢ hᵢσᶻᵢ. The source states: \"We specifically consider J = π/4, b = −π/4 for our analysis.\" Sites use Fin L, with finRotate L as the periodic successor; ↑ and ↓ are 0 and 1. The frozen localOp embeds a qubit matrix at its site, and qubitZ is the Pauli Z matrix. Real coefficients enter ℂ through ofReal; smul is scalar multiplication."),
            Node("hKick", "Kick Hamiltonian", KickFormula(),
                "Equation (1), p. 1, defines H_K = ∑ᵢ b σˣᵢ. Here b = −π/4; qubitX is the frozen Pauli X matrix."),
            Node("floquet", "Literal Floquet operator", FloquetFormula(),
                "Equation (2), p. 1: U = U_K U_I. The source states \"where U_I = e^{−i H_I} and U_K = e^{−i H_K}.\" The matrix exponentials are NormedSpace.exp, and I in Complex.I denotes the imaginary unit."),
            Node("initial", "Initial product state", InitialFormula(),
                "Equation (3), pp. 1–2: |ψ_{θ,φ}⟩ = ⊗ₖ (cos(θₖ/2)|↑⟩ + e^{iφₖ}sin(θₖ/2)|↓⟩). The formula displays the computational-basis amplitude at x. The letters theta and phi encode the Lean parameters θ and φ. All trigonometric arguments are real, and their values are embedded in ℂ by ofReal. The conditional ite(c,a,b) selects a when c holds and b otherwise."),
            Node("generic", "Generic states", GenericFormula(),
                "Page 2 states verbatim: \"States which do not belong to these class will henceforth be called generic.\" Equation (4) defines the transverse class by θₖ = π/2 for every site and the longitudinal class by θₖ ∈ {0,π} for every site. Thus generic excludes both classes, rather than imposing randomness or a measure-theoretic qualifier."),
            Node("renyiHalf", "Half-order Rényi entropy", RenyiFormula(),
                "Equation (9), p. 2, defines S_A^(α) = (1/(1−α)) log(tr(ρ_A^α)). At α = 1/2 this is twice the logarithm of the trace of the matrix square root. For density matrices cfc Real.sqrt is precisely that square root, and the trace is real. The real part makes the ℝ-valued expression explicit. On non-Hermitian inputs the real continuous functional calculus is zero. Anonymous bracket entries record the Lean typeclass arguments."),
            Node("contiguous", "Contiguous cyclic tripartition", ContiguousFormula(),
                "Page 2 states: \"In the following we now consider a tri-partition of state ABC with subsystem size L_A,L_B and L_C.\" The periodic chain is cut at a and b after a rotation by o. The three blocks are nonempty and disjoint and exhaust the sites. The val function extracts the natural value of a Fin index; the exponent o is a natural permutation power."),
            Node("joinParts", "Join subsystem coordinates", JoinFormula(),
                "The coordinates x, y and z lie on A, B and the complement of A ∪ B. The dependent conditional dite supplies membership proofs hA and hB to Subtype.mk. In the final branch hA and hB are nonmembership hypotheses, and Finset.notMem_union.mpr ⟨hA, hB⟩ proves membership in the complement. Outside is the frozen complement subtype. On disjoint blocks these assignments combine to one chain configuration, as used in the partial-trace expression on p. 2."),
            Node("reducedAB", "Joint reduced density matrix", ReducedFormula(),
                "Page 2 defines ρ_AB(t) = tr_C(|ψ(t)⟩⟨ψ(t)|). The coordinate function inside vecMulVec is the same ψ expressed on the product of the retained blocks and the complement. Its star is complex conjugation, so vecMulVec forms the rank-one density matrix. The frozen partialTraceRight sums over the complement."),
            Node("partialTranspose", "Partial transposition", TransposeFormula(),
                "Equation (5), p. 2, uses partial transposition with respect to B. It swaps the two B indices while preserving the A indices. This definition allows different subsystem dimensions; the existing partialTransposeB is used directly for the equal two-qubit matrix in the proof."),
            Node("evolved", "Integer-time evolution", EvolvedFormula(),
                "The source evolves the initial state with U_KI[h]^t (supplement, p. 6). The exponent is an integer power of the literal Floquet matrix, and Matrix.mulVec is its action on the amplitude vector. The counterexample uses t = 1."),
            Node("logNegativity", "Logarithmic negativity", NegativityFormula(),
                "Equation (5), p. 2: 𝓔(t) = ln tr(√((ρ_AB^{T_B}(t))†ρ_AB^{T_B}(t))). The frozen traceNorm is defined by precisely this trace-of-square-root expression, with conjTranspose as the adjoint. Real.log is the natural logarithm."),
            Node("mutualHalf", "Half-order Rényi mutual information", MutualFormula(),
                "Equation (9), p. 2: I_{A:B}^(α)(t) = S_A^(α)(t) + S_B^(α)(t) − S_AB^(α)(t). Here α = 1/2, partialTraceRight retains A and partialTraceLeft retains B."),
            Node("claim", "Pathak's Conjecture 1 at half order", ClaimFormula(),
                "Conjecture 1, p. 3, states verbatim: \"2𝓔(t) = I_{A:B}^{(α)}(t), hold for generic states at all times t.\" This is its α = 1/2 specialization, quantified over the chain length, real fields, product-state angles, contiguous tripartition and integer time. Each allowed tripartition has nonempty blocks. The specific fields are hᵢ = 1, with phases φᵢ = 0, for the counterexample."),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "Take L = 4, A = {0}, B = {1}, C = {2,3}, t = 1, hᵢ = 1 and φᵢ = 0. The initial state is |+⟩|+⟩|r⟩|r⟩, where |r⟩ = (2|0⟩+|1⟩)/√5, encoded by θ = (π/2,π/2,2 arctan(1/2),2 arctan(1/2)). It is generic. Factoring the commuting kick exponentials and the diagonal Ising exponential gives U = −W^{⊗4}G, with W a single-qubit unitary and G the periodic product of controlled-Z gates. The local unitaries preserve both measures. Before their action, the reduced density matrix has spectrum {16/25,4/25,4/25,1/25}; its partial transpose has spectrum {23/50,17/50,17/50,−7/50}, and both marginals are 1/2 times the identity. Hence 2𝓔(1) = log(1024/625) and I_{A:B}^(1/2)(1) = log(100/81). Strict injectivity of the logarithm on positive reals and the unequal rational arguments contradict the asserted equality. These finite-chain values do not settle a thermodynamic-limit identity at early times.",
                true)),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, bool derived = false) =>
        Describe.Lean(DescribeId.Create("pathak-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula),
            derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), derived ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula Num(int n) => new Formula.Number(n);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(F.Id(owner), Dot, F.Id(name));
    private static Formula QCall(string owner, string name, params Formula[] args) => new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, int n) => new Formula.Fraction(a, Num(n));
    private static Formula Neg(Formula a) => Sub(Num(0), Parenthesized(a));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Sites(Formula l) => Fin(l);
    private static Formula Configurations(Formula l) => Arrow(Sites(l), Fin(Num(2)));
    private static Formula Cartesian(Formula a, Formula b) => Seq(Parenthesized(a), Times, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, b));
    private static Formula Union(Formula a, Formula b) => Seq(a, Sp, Cup, Sp, b);
    private static Formula SubtypeOf(Formula a, Formula l) => Call("Subtype", Lambda("i", Sites(l), Mem(F.Id("i"), a)));
    private static Formula MatrixType(Formula n) => Call("Matrix", n, n, Complex());
    private static Formula OfReal(Formula a) => Call("ofReal", a);
    private static Formula Lambda(string name, Formula type, Formula body) => Seq(Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, type)), Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Prod, Seq(F.Id(name), Colon, type)), Parenthesized(body));
    private static Formula Instances(Formula n, Formula body) => Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp, OpenBracket, Call("DecidableEq", n), CloseBracket, Sp, body);
    private static Formula BiInstances(Formula a, Formula b, Formula body) => Seq(
        OpenBracket, Call("Fintype", a), CloseBracket, Sp, OpenBracket, Call("Fintype", b), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", a), CloseBracket, Sp, OpenBracket, Call("DecidableEq", b), CloseBracket, Sp, body);
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);

    private static Formula IsingFormula()
    {
        Formula l = F.Id("L"), h = F.Id("h"), i = F.Id("i");
        Formula interaction = SumOver("i", Sites(l), Mul(Call("localOp", i, F.Id("qubitZ")), Call("localOp", Apply(Call("finRotate", l), i), F.Id("qubitZ"))));
        Formula fields = SumOver("i", Sites(l), Smul(OfReal(Apply(h, i)), Call("localOp", i, F.Id("qubitZ"))));
        return Disp(All("L", Nat(), All("h", Arrow(Sites(l), Real()), Eqn(Call("hIsing", h), Add(Smul(OfReal(Div(Pi, 4)), interaction), fields)))));
    }
    private static Formula KickFormula()
    {
        Formula l = F.Id("L"), i = F.Id("i");
        return Disp(All("L", Nat(), Eqn(Call("hKick", l), Smul(OfReal(Div(Neg(Pi), 4)), SumOver("i", Sites(l), Call("localOp", i, F.Id("qubitX")))))));
    }
    private static Formula FloquetFormula()
    {
        Formula l = F.Id("L"), h = F.Id("h"), imaginary = Qualified("Complex", "I");
        return Disp(All("L", Nat(), All("h", Arrow(Sites(l), Real()), Eqn(Call("floquet", h),
            Mul(QCall("NormedSpace", "exp", Smul(Neg(imaginary), Call("hKick", l))), QCall("NormedSpace", "exp", Smul(Neg(imaginary), Call("hIsing", h))))))));
    }
    private static Formula InitialFormula()
    {
        Formula l = F.Id("L"), theta = F.Id("theta"), phi = F.Id("phi"), x = F.Id("x"), i = F.Id("i");
        Formula factor = Call("ite", Eqn(Apply(x, i), Num(0)), OfReal(QCall("Real", "cos", Div(Apply(theta, i), 2))),
            Mul(QCall("Complex", "exp", Mul(Qualified("Complex", "I"), OfReal(Apply(phi, i)))), OfReal(QCall("Real", "sin", Div(Apply(theta, i), 2)))));
        return Disp(All("L", Nat(), All("theta", Arrow(Sites(l), Real()), All("phi", Arrow(Sites(l), Real()), All("x", Configurations(l),
            Eqn(Apply(Call("initial", theta, phi), x), ProductOver("i", Sites(l), factor)))))));
    }
    private static Formula GenericFormula()
    {
        Formula l = F.Id("L"), theta = F.Id("theta"), i = F.Id("i");
        Formula body = And(new Formula.Not(Parenthesized(All("i", Sites(l), Eqn(Apply(theta, i), Div(Pi, 2))))),
            new Formula.Not(Parenthesized(All("i", Sites(l), Or(Eqn(Apply(theta, i), Num(0)), Eqn(Apply(theta, i), Pi))))));
        return Disp(All("L", Nat(), All("theta", Arrow(Sites(l), Real()), Iff(Call("generic", theta), body))));
    }
    private static Formula RenyiFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho");
        return Disp(All("n", F.Id("Type"), Instances(n, All("rho", MatrixType(n), Eqn(Call("renyiHalf", rho),
            Mul(Num(2), QCall("Real", "log", QCall("Complex", "re", QCall("Matrix", "trace", Call("cfc", Qualified("Real", "sqrt"), rho))))))))));
    }
    private static Formula ContiguousFormula()
    {
        Formula l = F.Id("L"), a = F.Id("a"), b = F.Id("b"), o = F.Id("o"), i = F.Id("i"), A = F.Id("A"), B = F.Id("B"), C = F.Id("C");
        Formula position = Call("val", Apply(Pow(Call("finRotate", l), o), i));
        Formula Filter(Formula condition) => QCall("Finset", "filter", Lambda("i", Sites(l), condition), Qualified("Finset", "univ"));
        Formula body = Ex("o", Nat(), Ex("a", Nat(), Ex("b", Nat(), And(Lt(Num(0), a), And(Lt(a, b), And(Lt(b, l),
            And(Eqn(A, Filter(Lt(position, a))), And(Eqn(B, Filter(And(Le(a, position), Lt(position, b)))), Eqn(C, Filter(Le(b, position)))))))))));
        return Disp(All("L", Nat(), All("A", Call("Finset", Sites(l)), All("B", Call("Finset", Sites(l)), All("C", Call("Finset", Sites(l)), Iff(Call("contiguous", A, B, C), body))))));
    }
    private static Formula JoinFormula()
    {
        Formula l = F.Id("L"), A = F.Id("A"), B = F.Id("B"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), i = F.Id("i"), hA = new Formula.Symbol(FormulaIdentifier.Create("hA")), hB = F.Id("hB");
        Formula aCondition = Mem(i, A), bCondition = Mem(i, B);
        Formula body = Call("dite", aCondition, Lambda("hA", aCondition, Apply(x, QCall("Subtype", "mk", i, hA))),
            Lambda("hA", new Formula.Not(aCondition), Call("dite", bCondition, Lambda("hB", bCondition, Apply(y, QCall("Subtype", "mk", i, hB))),
                Lambda("hB", new Formula.Not(bCondition), Apply(z, QCall("Subtype", "mk", i,
                    Apply(Seq(F.Id("Finset"), Dot, new Formula.Subscript(F.Id("notMem"), F.Id("union")), Dot, F.Id("mpr")),
                        Seq(Langle, hA, Comma, Sp, hB, Rangle))))))));
        return Disp(All("L", Nat(), All("A", Call("Finset", Sites(l)), All("B", Call("Finset", Sites(l)),
            All("x", Arrow(SubtypeOf(A, l), Fin(Num(2))), All("y", Arrow(SubtypeOf(B, l), Fin(Num(2))),
            All("z", Arrow(Call("Outside", Union(A, B)), Fin(Num(2))), All("i", Sites(l), Eqn(Apply(Call("joinParts", A, B, x, y, z), i), body)))))))));
    }
    private static Formula ReducedFormula()
    {
        Formula l = F.Id("L"), A = F.Id("A"), B = F.Id("B"), psi = F.Id("psi"), p = F.Id("p");
        Formula coordinates = Cartesian(Cartesian(Arrow(SubtypeOf(A, l), Fin(Num(2))), Arrow(SubtypeOf(B, l), Fin(Num(2)))), Arrow(Call("Outside", Union(A, B)), Fin(Num(2))));
        Formula amplitudes = Lambda("p", coordinates, Apply(psi, Call("joinParts", A, B, Call("fst", Call("fst", p)), Call("snd", Call("fst", p)), Call("snd", p))));
        return Disp(All("L", Nat(), All("A", Call("Finset", Sites(l)), All("B", Call("Finset", Sites(l)), All("psi", Arrow(Configurations(l), Complex()),
            Eqn(Call("reducedAB", A, B, psi), Call("partialTraceRight", QCall("Matrix", "vecMulVec", amplitudes, Call("star", amplitudes)))))))));
    }
    private static Formula TransposeFormula()
    {
        Formula A = F.Id("A"), B = F.Id("B"), rho = F.Id("rho"), p = F.Id("p"), q = F.Id("q"), pair = Cartesian(A, B);
        return Disp(All("A", F.Id("Type"), All("B", F.Id("Type"), All("rho", MatrixType(pair), All("p", pair, All("q", pair,
            Eqn(Apply(Call("partialTranspose", rho), p, q), Apply(rho, Pair(Call("fst", p), Call("snd", q)), Pair(Call("fst", q), Call("snd", p))))))))));
    }
    private static Formula EvolvedFormula()
    {
        Formula l = F.Id("L"), h = F.Id("h"), theta = F.Id("theta"), phi = F.Id("phi"), t = F.Id("t");
        return Disp(All("L", Nat(), All("h", Arrow(Sites(l), Real()), All("theta", Arrow(Sites(l), Real()), All("phi", Arrow(Sites(l), Real()), All("t", Int(),
            Eqn(Call("evolved", h, theta, phi, t), QCall("Matrix", "mulVec", Pow(Call("floquet", h), t), Call("initial", theta, phi)))))))));
    }
    private static Formula NegativityFormula()
    {
        Formula A = F.Id("A"), B = F.Id("B"), rho = F.Id("rho");
        return Disp(All("A", F.Id("Type"), All("B", F.Id("Type"), BiInstances(A, B, All("rho", MatrixType(Cartesian(A, B)),
            Eqn(Call("logNegativity", rho), QCall("Real", "log", Call("traceNorm", Call("partialTranspose", rho)))))))));
    }
    private static Formula MutualFormula()
    {
        Formula A = F.Id("A"), B = F.Id("B"), rho = F.Id("rho");
        Formula body = Sub(Add(Call("renyiHalf", Call("partialTraceRight", rho)), Call("renyiHalf", Call("partialTraceLeft", rho))), Call("renyiHalf", rho));
        return Disp(All("A", F.Id("Type"), All("B", F.Id("Type"), BiInstances(A, B, All("rho", MatrixType(Cartesian(A, B)), Eqn(Call("mutualHalf", rho), body))))));
    }
    private static Formula ClaimFormula()
    {
        Formula l = F.Id("L"), h = F.Id("h"), theta = F.Id("theta"), phi = F.Id("phi"), t = F.Id("t"), A = F.Id("A"), B = F.Id("B"), C = F.Id("C");
        Formula rho = Call("reducedAB", A, B, Call("evolved", h, theta, phi, t));
        Formula conclusion = Implies(Call("contiguous", A, B, C), Implies(Call("generic", theta), Eqn(Mul(Num(2), Call("logNegativity", rho)), Call("mutualHalf", rho))));
        Formula body = All("L", Nat(), All("h", Arrow(Sites(l), Real()), All("theta", Arrow(Sites(l), Real()), All("phi", Arrow(Sites(l), Real()),
            All("A", Call("Finset", Sites(l)), All("B", Call("Finset", Sites(l)), All("C", Call("Finset", Sites(l)), All("t", Int(), conclusion))))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
