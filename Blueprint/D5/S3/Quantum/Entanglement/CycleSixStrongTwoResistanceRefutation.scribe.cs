using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class CycleSixStrongTwoResistanceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.";
    private static readonly LibraryNoteRef Han = LibraryNoteRef.Create("D5/L/QuantumStates/han2026resistant");
    private static readonly LibraryNoteRef Zhang = LibraryNoteRef.Create("D5/L/QuantumStates/zhang2025resistant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-cycle graph state is not strongly 2-resistant: tracing out qubits 0 and 2 leaves a convex combination of products across the cut {1} | {3,4,5}. The C5 clause of the question is not answered here.",
        H("The six-cycle graph state is not strongly 2-resistant"),
        Blocks(
            Node("IsFullySeparable", "Full separability", FullySeparableFormula(),
                "Zhang et al., arXiv:2505.06567v1, page 2, equation (1): \"A state is fully separable if it can be written as a convex combination of product states,\". Han, Zhang and Zhang, arXiv:2606.08561v1, page 2, Section II.A: \"A mixed state ρ on H₁ ⊗ · · · ⊗ H_N is called fully separable if it can be written as\" the displayed convex sum, \"where p_α ≥ 0, ∑_α p_α = 1, and each ρ_i^(α) is a one-particle density operator\". V labels the qubits, configurations are functions V -> Bool, and DensityState is the positive semidefinite trace-one complex matrix carrier. The map val forgets the density-state proof. Real weights are embedded into C in the entrywise equality.", Han),
            Node("IsBiseparable", "Biseparability with explicit qubit reindexing", BiseparableFormula(),
                "Zhang et al., arXiv:2505.06567v1, page 2, following equation (3): \"where the first sum goes over all bipartitions of [N]. If a state does admit such a decomposition, it is called biseparable\". A_j and its complement are nonempty subsets of V. In a carrier position a finite set denotes its subtype, and (j : Fin k) -> T(j) denotes a dependent function type. Restricting x and y to these complementary subsets explicitly pulls back sigma_j tensor tau_j to the original configuration basis. The finite mixture permits different cuts in different terms; flattening the two finite convex sums in equation (3) gives this single sum.", Zhang),
            Node("IsGME", "Genuine multipartite entanglement", GmeFormula(),
                "Zhang et al., arXiv:2505.06567v1, page 2: \"An N-particle state ρ on Hilbert space H₁ ⊗ · · · ⊗ H_N is genuinely entangled if it cannot be decomposed into as\" equation (3), the convex mixture across bipartitions. Thus GME is the negation of biseparability. These predicates are applied to normalized density matrices in the state question.", Zhang),
            Node("joinBits", "Joining lost and retained configurations", JoinFormula(),
                "In a carrier position J denotes the subtype {w : V | w is in J}, and {w : V | w is not in J} denotes the complementary subtype. The dependent conditional dite joins z and x by the membership test. Its first h binder carries a membership proof and its second h binder carries a nonmembership proof; the angle brackets are the actual subtype constructors. Proof irrelevance makes the branch values independent of the proof terms. The function restrictions and this join are inverse coordinate maps between V -> Bool and (J -> Bool) times ({w : V | w is not in J} -> Bool).", null),
            Node("partialTrace", "Finite partial trace over a loss set", TraceFormula(),
                "Zhang et al., arXiv:2505.06567v1, page 2: \"Take the partial trace over all particles in J ⊂ [N], and denote the reduced state\" ρ_J̄(ψ) ≜ Tr_J(|ψ⟩⟨ψ|), equation (2). Here the finite sum is the existing bipartite partialTraceFirst after reindexing with joinBits: the same traced configuration z appears in the row and column. This definition also applies to a general input matrix rho.", Zhang),
            Node("cycleGraphState", "Cycle graph-state amplitudes", CycleFormula(),
                "Han, Zhang and Zhang, arXiv:2606.08561v1, page 2, Section II.B: \"The graph state |G⟩ is obtained by preparing each qubit in\" |+⟩ = (|0⟩ + |1⟩)/√2 \"and applying a controlled-Z gate along each edge:\" |G⟩ = (∏_{{u,v} ∈ E} CZ_uv)|+⟩^⊗N. Qubits are numbered 0,...,n-1, Bool.toNat sends false to 0 and true to 1. NatMod(a,n) denotes Nat.mod a n, the natural-number remainder. The angle brackets denote the Fin n element whose value is the displayed remainder; the successor index uses val(i)+1 modulo n. For n >= 3 the edge sum counts each edge of C_n once, so this controlled-Z definition gives the displayed amplitudes. The square root and division are in R and C respectively; the formula also defines a vector for other positive n.", Han),
            Node("IsStrongResistant", "Strong resistance to particle loss", StrongFormula(),
                "Zhang et al., arXiv:2505.06567v1, page 3, Definition 2: \"A genuinely entangled state |ϕ⟩ is called strong m-resistant if it satisfies the following properties: 1) ρ_J̄(ϕ) is genuinely entangled for any J ⊂ [N] with |J| = m. 2) ρ_J̄(ϕ) is fully separable for any J ⊂ [N] with |J| = m + 1.\" The initial genuinely entangled state supplies the first conjunct. Fin n replaces [N] by zero-based labels, losses are finite subsets, and psi is the amplitude vector; vecMulVec(psi,star(psi)) is |psi><psi|. The two universal quantifiers retain both loss conditions verbatim.", Zhang),
            Node("claim", "The C6 clause of the published question", ClaimFormula(),
                "Han, Zhang and Zhang, arXiv:2606.08561v1, page 8, Discussion: \"Several open problems remain. First, do C₅ and C₆ give strongly m-resistant graph states for m = 1 and m = 2, respectively? Here, “strong” means genuine multipartite entanglement rather than mere entanglement.\". This claim encodes only the C6, m = 2 clause, on labels 0,...,5 with amplitudes (-1) raised to the cyclic edge phase, divided by 8. The C5, m = 1 clause remains open here.", Han),
            Describe.Lean(DescribeId.Create("cycle-six-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A two-qubit loss destroys genuine multipartite entanglement"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Han),
                Blocks(Paragraph(Text("For J = {0,2}, write the traced bits as t,u and the retained bits as r,x,y,z on qubits 1,3,4,5. The six-cycle phase splits as (t+u)r + xy + yz + ux + tz. Set a_tu(r) = (-1)^((t+u)r) and b_tu(x,y,z) = (-1)^(xy+yz+ux+tz). The marginal is (1/4) times the sum over the four t,u of (a_tu a_tu* / 2) tensor (b_tu b_tu* / 8). Each factor is positive semidefinite with trace one, and the four nonnegative weights sum to one. This is a product mixture across the nontrivial cut {1} | {3,4,5}; it is biseparable and violates the requirement that every two-qubit-loss marginal be GME."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("han-zhang-zhang-2026-cycle-six-strong-two-resistance-refutation"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, LibraryNoteRef? source) =>
        Describe.Lean(DescribeId.Create("cycle-six-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula),
            source is null ? AssessedProvenance.FromRepo() : AssessedProvenance.FromLiterature(source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Arr(Formula a, Formula b) => Seq(Parenthesized(a), To, Sp, b);
    private static Formula Bits(Formula v) => Arr(v, F.Id("Bool"));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Dens(Formula v) => Call("DensityState", v);
    private static Formula Mat(Formula v) => Call("Matrix", Bits(v), Bits(v), Complex());
    private static Formula All(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Ex(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), type, body);
    private static Formula PiType(string v, Formula type, Formula body) =>
        Seq(Parenthesized(Seq(F.Id(v), Colon, type)), To, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Apply(Formula a, params Formula[] args) => new Formula.Apply(a, [.. args]);
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula Complement(Formula a) => new Formula.Power(a, F.Id("c"));
    private static Formula Restrict(Formula x, Formula domain) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id("v"), Colon, domain)),
            Comma, Sp, Apply(x, Val(F.Id("v")))));
    private static Formula SumOver(string v, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(v), Colon, type)), Sp, Parenthesized(body));
    private static Formula ProductOver(string v, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(F.Id(v), Colon, type)), Sp, Parenthesized(body));
    private static Formula Instances(Formula v, Formula body, bool finite = true) => finite
        ? Seq(OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Comma, Sp, body)
        : Seq(OpenBracket, Call("DecidableEq", v), CloseBracket, Comma, Sp, body);
    private static Formula Context(Formula body) => All("V", F.Id("Type"), Instances(F.Id("V"), body));
    private static Formula WeightConditions(Formula p, Formula k, Formula rest) =>
        And(All("j", FinOf(k), Leq(D(0), Apply(p, F.Id("j")))),
            And(Eqn(SumOver("j", FinOf(k), Apply(p, F.Id("j"))), D(1)), rest));
    private static Formula FullySeparableFormula()
    {
        Formula v = F.Id("V"), rho = F.Id("rho"), k = F.Id("k"), p = F.Id("p"), sigma = F.Id("sigma"), j = F.Id("j");
        Formula entry = Mul(Call("ofReal", Apply(p, j)), ProductOver("v", v,
            Apply(Val(Apply(sigma, j, F.Id("v"))), Apply(F.Id("x"), F.Id("v")), Apply(F.Id("y"), F.Id("v")))));
        Formula equality = All("x", Bits(v), All("y", Bits(v), Eqn(Apply(rho, F.Id("x"), F.Id("y")), SumOver("j", FinOf(k), entry))));
        Formula body = Ex("k", Nat(), Ex("p", Arr(FinOf(k), Real()),
            Ex("sigma", Arr(FinOf(k), Arr(v, Dens(F.Id("Bool")))), WeightConditions(p, k, equality))));
        return Disp(Context(All("rho", Mat(v), IffTo(Call("IsFullySeparable", rho), body))));
    }
    private static Formula BiseparableFormula()
    {
        Formula v = F.Id("V"), rho = F.Id("rho"), k = F.Id("k"), p = F.Id("p"), j = F.Id("j"), aj = Apply(F.Id("A"), j);
        Formula cuts = All("j", FinOf(k), And(Call("Nonempty", aj), Call("Nonempty", Complement(aj))));
        Formula entry = Mul(Mul(Call("ofReal", Apply(p, j)),
            Apply(Val(Apply(F.Id("sigma"), j)), Restrict(F.Id("x"), aj), Restrict(F.Id("y"), aj))),
            Apply(Val(Apply(F.Id("tau"), j)), Restrict(F.Id("x"), Complement(aj)), Restrict(F.Id("y"), Complement(aj))));
        Formula equality = All("x", Bits(v), All("y", Bits(v), Eqn(Apply(rho, F.Id("x"), F.Id("y")), SumOver("j", FinOf(k), entry))));
        Formula body = Ex("k", Nat(), Ex("p", Arr(FinOf(k), Real()), Ex("A", Arr(FinOf(k), Call("Finset", v)),
            Ex("sigma", PiType("j", FinOf(k), Dens(Bits(aj))),
            Ex("tau", PiType("j", FinOf(k), Dens(Bits(Complement(aj)))), WeightConditions(p, k, And(cuts, equality)))))));
        return Disp(Context(All("rho", Mat(v), IffTo(Call("IsBiseparable", rho), body))));
    }
    private static Formula GmeFormula() => Disp(Context(All("rho", Mat(F.Id("V")),
        IffTo(Call("IsGME", F.Id("rho")), new Formula.Not(Call("IsBiseparable", F.Id("rho")))))));
    private static Formula Retained(Formula v, Formula j) => Seq(OpenBrace, F.Id("w"), Colon, v, Mid,
        new Formula.Not(new Formula.Relation(F.Id("w"), FormulaRelationOperator.MemberOf, j)), CloseBrace);
    private static Formula JoinFormula()
    {
        Formula v = F.Id("V"), j = F.Id("J"), z = F.Id("z"), x = F.Id("x"), q = F.Id("v");
        Formula condition = new Formula.Relation(q, FormulaRelationOperator.MemberOf, j);
        Formula h = F.Id("h");
        Formula pair = Seq(Langle, Sp, q, Comma, h, Rangle);
        Formula branch = Call("dite", condition,
            Parenthesized(Seq(LambdaLower, Sp, h, Comma, Sp, Apply(z, pair))),
            Parenthesized(Seq(LambdaLower, Sp, h, Comma, Sp, Apply(x, pair))));
        Formula body = All("J", Call("Finset", v), All("z", Bits(j), All("x", Bits(Retained(v, j)),
            All("v", v, Eqn(Call("joinBits", j, z, x, q), branch)))));
        return Disp(All("V", F.Id("Type"), Instances(v, body, false)));
    }
    private static Formula TraceFormula()
    {
        Formula v = F.Id("V"), j = F.Id("J"), rho = F.Id("rho"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula equality = Eqn(Apply(Call("partialTrace", rho, j), x, y),
            SumOver("z", Bits(j), Apply(rho, Call("joinBits", j, z, x), Call("joinBits", j, z, y))));
        return Disp(Context(All("rho", Mat(v), All("J", Call("Finset", v),
            All("x", Bits(Retained(v, j)), All("y", Bits(Retained(v, j)), equality))))));
    }
    private static Formula CycleFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), i = F.Id("i");
        Formula next = Seq(Langle, Call("NatMod", Add(Val(i), D(1)), n), Rangle);
        Formula phase = SumOver("i", FinOf(n), Mul(Call("toNat", Apply(x, i)), Call("toNat", Apply(x, next))));
        Formula value = new Formula.Fraction(new Formula.Power(Parenthesized(new Formula.Negate(D(1))), phase),
            Call("ofReal", Seq(Sqrt, Grp(new Formula.Power(D(2), n)))));
        return Disp(All("n", Nat(), Seq(OpenBracket, Call("NeZero", n), CloseBracket, Comma, Sp,
            All("x", Bits(FinOf(n)), Eqn(Call("cycleGraphState", n, x), value)))));
    }
    private static Formula Pure(Formula psi) => Call("vecMulVec", psi, Call("star", psi));
    private static Formula StrongFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), psi = F.Id("psi"), j = F.Id("J");
        Formula loss = All("J", Call("Finset", FinOf(n)), Imp(Eqn(Call("card", j), m), Call("IsGME", Call("partialTrace", Pure(psi), j))));
        Formula extraLoss = All("J", Call("Finset", FinOf(n)), Imp(Eqn(Call("card", j), Add(m, D(1))), Call("IsFullySeparable", Call("partialTrace", Pure(psi), j))));
        return Disp(All("n", Nat(), All("m", Nat(), All("psi", Arr(Bits(FinOf(n)), Complex()),
            IffTo(Call("IsStrongResistant", m, psi), And(Call("IsGME", Pure(psi)), And(loss, extraLoss)))))));
    }
    private static Formula ClaimFormula() => Disp(IffTo(F.Id("claim"), Call("IsStrongResistant", D(2), Call("cycleGraphState", D(6)))));
}
