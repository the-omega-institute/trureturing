using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class BroadcastingChannelExtremaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mitra2021layers");
    private const string Questions =
        "Section III.A, p. 5: “For an observable, in this way, one can get the set of different broadcasting channels that broadcast the observable. It is an open question whether this set has the highest element i.e., a broadcasting channel in this set from which all other broadcasting channels that can broadcast the observable, can be constructed through concatenation with nondisturbing channels. It is also an open question whether this set has the lowest element i.e., a broadcasting channel in this set which can be constructed from all other broadcasting channels that broadcast the observable through concatenation with nondisturbing channels.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-dimensional observable with two outcomes has a nonempty set of broadcasting channels and has neither extremum under nondisturbing precomposition.",
        H("Broadcasting channels need have neither extremum"),
        Blocks(
            Node("density_le_one", "Density matrices are contractions", Disp(All("n", Call("Type"), Seq(OpenBracket, Call("Fintype", V("n")), CloseBracket, Sp, OpenBracket, Call("DecidableEq", V("n")), CloseBracket, Comma, Sp, All("T", MatrixType(V("n"), V("n")), Implies(At(Qualified("Matrix", "PosSemidef"), V("T")), Implies(Equal(Trace(V("T")), D(1)), At(Qualified("Matrix", "PosSemidef"), new Formula.Binary(D(1), FormulaBinaryOperator.Subtract, V("T"))))))))), "Every positive semidefinite complex matrix of trace one is bounded above by the identity in the positive semidefinite order.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("IsChannel", "Finite Kraus channels", ChannelFormula(),
                "Section II.B, p. 2: “A CPTP map Θ : S(Hin) → S(Hout) is called a quantum channel, where Hin and Hout are two Hilbert spaces [15].” Finite Kraus form expresses complete positivity and trace preservation. MatrixMap.of_kraus is the frozen operation; its action is the finite sum of K(j) X conjTranspose(K(j)). The output index type iota has anonymous Fintype and DecidableEq instances.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Broadcasts", "Broadcasting an observable", BroadcastingFormula(),
                "Definition 1, p. 2: “A channel Λ : S(H) → S(H_A ⊗ H_B) with H_A = H_B = H is called a broadcasting channel.” Definition 3, p. 3: “An observable A ∈ O_X^d is broadcast by a broadcasting channel Λ ∈ C_broad^d if for all ρ ∈ S(H), x ∈ X” followed by equation (5), Tr[ρA(x)] = Tr[Λ(ρ)A(x) ⊗ I] = Tr[Λ(ρ)I ⊗ A(x)]. Outcomes are Fin m, and each subsystem is indexed by Fin d. The state predicate is the SLDSpectralEnergy.IsDensity: positive semidefinite with trace one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Nondisturbing", "Nondisturbing channels", NondisturbingFormula(),
                "Definition 8, p. 5: “A channel Θ : S(H) → S(H) is nondisturbing with respect to an observable A if for all ρ ∈ S(H),” followed by equation (22), Tr[ρA(x)] = Tr[Θ(ρ)A(x)] for all x ∈ Ω_A. The displayed formula uses this trace form, equivalent to the dual form in equation (23).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ConstructedFrom", "Nondisturbing precomposition", OrderFormula(),
                "Section III.A, p. 5 uses concatenation with nondisturbing channels. ConstructedFrom A Lprime L states that Lprime = L ∘ Theta for such a channel Theta. Equality is equality on all complex matrices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("HasHighest", "Highest element", ExtremumFormula(true),
                Questions + " HasHighest requires a broadcasting channel H from which every broadcasting channel L is obtained by nondisturbing precomposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("HasLowest", "Lowest element", ExtremumFormula(false),
                Questions + " HasLowest requires a broadcasting channel H obtained from every broadcasting channel L by nondisturbing precomposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The two extremum questions", ClaimFormula(),
                Questions + " The universal encoding quantifies over natural dimensions d, outcome counts m, and all observables A. The frozen ConcealmentKernelNecessityRefutation.IsPOVM means that every effect is positive semidefinite and their sum is I. Nonemptiness of the broadcasting set is explicit. The disjunction allows either extremum; its negation exhibits one observable lacking both.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Both answers can be negative", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Take d = 3, m = 2, P = diag(1,1,0), Q = I − P, A(0) = (3/4)P + (1/4)Q, and A(1) = I − A(0). Three broadcasting channels prepare the matrix units at (0,0), (1,1), and (0,1) on the P sector and at (2,2) on the Q sector. Preservation of A(0) and trace forces preservation of P. ConcealmentKernelNecessityRefutation.dual_kraus identifies the dual effect. The balanced state on coordinates zero and two is ActualQubitChordObstruction.signalProbe 1. Together with the other normalized real and imaginary pure states it determines the dual effect on all matrices, so nondisturbing precomposition fixes each of the three channels. Their inequality excludes a lowest element. FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero applied to I − P places the three input states of a highest element in the P sector. They would produce three orthogonal pure outputs. Positivity and the dual Kraus completeness identity bound their total trace by trace(P) = 2, although each output contributes at least one. Thus 3 ≤ 2, a contradiction. Only this three-dimensional, two-outcome instance is asserted; the rank-r family and the qubit and sharp-observable questions remain open here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mitra-2021-broadcasting-channel-extrema"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("broadcasting-extrema-" + name.Replace("_", "").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Field(string name) => Seq(Mathbb, Grp(V(name)));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula MatrixType(Formula rows, Formula columns) => Call("Matrix", rows, columns, Field("C"));
    private static Formula Mat(Formula d) => MatrixType(Fin(d), Fin(d));
    private static Formula Out(Formula d) => MatrixType(Product(Fin(d), Fin(d)), Product(Fin(d), Fin(d)));
    private static Formula Fun(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Trace(Formula matrix) => At(Qualified("Matrix", "trace"), matrix);
    private static Formula Adjoint(Formula matrix) => At(Qualified("Matrix", "conjTranspose"), matrix);
    private static Formula Kron(Formula a, Formula b) => At(Qualified("Matrix", "kronecker"), a, b);
    private static Formula Density(Formula matrix) => At(Qualified("SLDSpectralEnergy", "IsDensity"), matrix);
    private static Formula Observable(Formula a) => At(Qualified("ConcealmentKernelNecessityRefutation", "IsPOVM"), a);
    private static Formula Parameters(Formula body) => All("d", Field("N"), All("m", Field("N"), All("A", Fun(Fin(V("m")), Mat(V("d"))), body)));

    private static Formula ChannelFormula()
    {
        Formula d = V("d"), iota = V("iota"), k = V("k"), j = V("j"), K = V("K"), x = V("X"), phi = V("Phi");
        Formula completeness = Equal(Seq(Sum, Underscore, Grp(j, Sp, Colon, Sp, Fin(k)), Sp,
            Parenthesized(Mul(Adjoint(At(K, j)), At(K, j)))), D(1));
        Formula action = All("X", Mat(d), Equal(At(phi, x), At(
            Seq(Operatorname, Grp(V("MatrixMap")), Dot, Operatorname, Grp(V("of")), Underscore, Grp(V("kraus"))),
            K, K, x)));
        Formula body = Iff(Call("IsChannel", phi), Some("k", Field("N"), Some("K", Fun(Fin(k), MatrixType(iota, Fin(d))), And(completeness, action))));
        return Disp(All("d", Field("N"), All("iota", V("Type"), Seq(
            OpenBracket, Call("Fintype", iota), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", iota), CloseBracket, Sp,
            All("Phi", Fun(Mat(d), MatrixType(iota, iota)), body)))));
    }

    private static Formula BroadcastingFormula()
    {
        Formula d = V("d"), a = V("A"), l = V("L"), rho = V("rho"), x = V("x"), ax = At(a, x);
        Formula probability = Trace(Mul(rho, ax));
        Formula marginals = And(Equal(Trace(Mul(At(l, rho), Kron(ax, D(1)))), probability),
            Equal(Trace(Mul(At(l, rho), Kron(D(1), ax))), probability));
        Formula body = And(Call("IsChannel", l), All("rho", Mat(d), Implies(Density(rho), All("x", Fin(V("m")), marginals))));
        return Disp(Parameters(All("L", Fun(Mat(d), Out(d)), Iff(Call("Broadcasts", a, l), body))));
    }

    private static Formula NondisturbingFormula()
    {
        Formula d = V("d"), a = V("A"), t = V("Theta"), rho = V("rho"), x = V("x");
        Formula body = And(Call("IsChannel", t), All("rho", Mat(d), Implies(Density(rho), All("x", Fin(V("m")),
            Equal(Trace(Mul(At(t, rho), At(a, x))), Trace(Mul(rho, At(a, x))))))));
        return Disp(Parameters(All("Theta", Fun(Mat(d), Mat(d)), Iff(Call("Nondisturbing", a, t), body))));
    }

    private static Formula OrderFormula()
    {
        Formula d = V("d"), a = V("A"), l = V("L"), lp = V("Lprime"), t = V("Theta");
        Formula body = Some("Theta", Fun(Mat(d), Mat(d)), And(Call("Nondisturbing", a, t),
            Equal(lp, Seq(l, Sp, Circ, Sp, t))));
        return Disp(Parameters(All("Lprime", Fun(Mat(d), Out(d)), All("L", Fun(Mat(d), Out(d)),
            Iff(Call("ConstructedFrom", a, lp, l), body)))));
    }

    private static Formula ExtremumFormula(bool highest)
    {
        Formula d = V("d"), a = V("A"), h = V("H"), l = V("L");
        Formula order = highest ? Call("ConstructedFrom", a, l, h) : Call("ConstructedFrom", a, h, l);
        Formula body = Some("H", Fun(Mat(d), Out(d)), And(Call("Broadcasts", a, h),
            All("L", Fun(Mat(d), Out(d)), Implies(Call("Broadcasts", a, l), order))));
        return Disp(Parameters(Iff(Call(highest ? "HasHighest" : "HasLowest", a), body)));
    }

    private static Formula ClaimFormula() => Disp(Iff(V("claim"), ClaimBody()));

    private static Formula ClaimBody()
    {
        Formula d = V("d"), a = V("A"), l = V("L");
        Formula body = Implies(Observable(a), Implies(Some("L", Fun(Mat(d), Out(d)), Call("Broadcasts", a, l)),
            Or(Call("HasHighest", a), Call("HasLowest", a))));
        return Parameters(body);
    }
}
