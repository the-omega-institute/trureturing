using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class LeeYangPhaseShiftedParityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/wong2026leeyang");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pi-flux four-cycle refutes the phase-shifted parity conjecture.",
        H("The odd-sector spectral minimum need not be the second eigenvalue"),
        Blocks(
            Node("hpq", "The two-qubit interaction", LocalTerm(),
                "Section 5.6, p. 26: “Define a two-qubit operator h(z) = |00⟩⟨00| + z|11⟩⟨00| + z*|00⟩⟨11| + |z|²|11⟩⟨11|, where z ∈ ℂ.” Computational basis states are functions Fin n → Fin 2. The matrix entry with row y and column x vanishes unless all other qubits agree. The complex conjugate is starRingEnd ℂ applied to z, and Complex.normSq z is cast through ℝ to ℂ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("H", "The phase-shifted Hamiltonian", Hamiltonian(),
                "Section 5.6, p. 26: “A phase-shifted EPR-like Hamiltonian is defined as H_s(θ) = −Σ_{(p,q)∈E} h_{p,q}(se^{iθ_{p,q}}), (77) where s ∈ [0,1] and θ_{p,q} ∈ [0,2π) are arbitrary edge-dependent angles (phase shifts). Setting θ_{p,q} = 0 gives the original EPR-like Hamiltonian H_s.” Each undirected edge is counted once, using p < q. Real angles supply representatives in the exponential. Complex.I is the imaginary unit.",
                AssessedProvenance.FromLiterature(Source)),
            Node("eigAsc", "Eigenvalues in increasing order", Eigenvalues(),
                "For a Hermitian matrix, sort the multiset of Matrix.IsHermitian.eigenvalues in increasing order, retaining multiplicity. Return the empty list for a matrix that is not Hermitian. The proof h in the conditional selects the Hermitian eigenvalues.",
                AssessedProvenance.FromRepo(Source)),
            Node("claim", "Conjecture 2 with arbitrary edge phases", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "Conjecture 2, Section 5.5, p. 24: “Suppose n ≥ 2, s ∈ [0, 1), and the interaction graph is connected. Then the second smallest eigenvalue of H_s coincides with the smallest eigenvalue of H_s restricted to the odd-weight subspace.” Section 5.6, p. 26: “We leave as an open question whether Conjectures 1,2,3 hold for phase-shifted EPR-like Hamiltonians.” This proposition extends Conjecture 2 to every phase function. List.getD uses zero-based indices: index one is the second eigenvalue with multiplicity and index zero is the odd-sector minimum. Matrix.submatrix restricts to the odd-weight computational basis.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "A four-cycle refutes the extension", Disp(Seq(F.Neg, Sp, Parenthesized(ClaimBody()))),
                "Take s = 3/5 and the cycle with edges {0,1}, {0,3}, {1,2}, {2,3}. The phase on {0,3} is π and the other phases are zero. Two distinct full-space eigenvalues are below −5/2, while every odd-sector eigenvalue is above −5/2. The odd matrix satisfies 25M² + 68M + 18I = 0; two explicit full-space eigenvectors give eigenvalues −(67 + √1989)/25 and −(35 + √901)/25. Sorting with multiplicity therefore puts the second full-space eigenvalue strictly below the odd-sector minimum. This conclusion concerns the phase-shifted extension; it leaves Conjecture 2 for zero phases unresolved.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wong-bravyi-gosset-liu-2026-conjecture-2-phase-shifted-extension"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("lee-yang-phase-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Arrow(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, variable, Colon, Sp, type, Comma, Sp, body));
    private static Formula Fn(Formula domain, Formula codomain) => Seq(Parenthesized(domain), Sp, To, Sp, codomain);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Bits(Formula n) => Fn(Fin(n), Fin(D(2)));
    private static Formula MatrixType(Formula index) => Call("Matrix", index, index, Complexes());
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Sum(Formula variable, Formula type, Formula body) =>
        Call("Finset.sum", Named("Finset.univ"), Lam(variable, type, body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Call("ite", Parenthesized(condition), yes, no);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula LocalTerm()
    {
        Formula n = F.Id("n"), p = F.Id("p"), q = F.Id("q"), z = F.Id("z"),
            x = F.Id("x"), y = F.Id("y"), k = F.Id("k");
        Formula Indicator(Formula a, Formula b, Formula coefficient) => If(
            And(Equal(App(x, p), a), And(Equal(App(x, q), a), And(Equal(App(y, p), b), Equal(App(y, q), b)))), coefficient, D(0));
        Formula same = All(k, Fin(n), Arrow(Relation(k, FormulaRelationOperator.NotEqual, p),
            Arrow(Relation(k, FormulaRelationOperator.NotEqual, q), Equal(App(y, k), App(x, k)))));
        Formula terms = Add(Add(Add(Indicator(D(0), D(0), D(1)), Indicator(D(0), D(1), z)),
            Indicator(D(1), D(0), App(Call("starRingEnd", Complexes()), z))),
            Indicator(D(1), D(1), Cast(Cast(Call("Complex.normSq", z), Reals()), Complexes())));
        return Disp(All(n, Nats(), All(p, Fin(n), All(q, Fin(n), All(z, Complexes(),
            Equal(Call("hpq", p, q, z), Lam(y, Bits(n), Lam(x, Bits(n), If(same, terms, D(0))))))))));
    }

    private static Formula Hamiltonian()
    {
        Formula n = F.Id("n"), g = F.Id("G"), s = F.Id("s"), theta = Theta,
            p = F.Id("p"), q = F.Id("q");
        Formula phase = Mul(Cast(s, Complexes()), Call("Complex.exp",
            Mul(Cast(Cast(App(theta, p, q), Reals()), Complexes()), Named("Complex.I"))));
        Formula summand = If(And(Relation(p, FormulaRelationOperator.LessThan, q), App(Named("G.Adj"), p, q)),
            Call("hpq", p, q, phase), D(0));
        return Disp(All(n, Nats(), All(g, Call("SimpleGraph", Fin(n)),
            Instance(Call("DecidableRel", Named("G.Adj")), All(s, Reals(), All(theta, Fn(Fin(n), Fn(Fin(n), Reals())),
                Equal(Call("H", g, s, theta), Seq(Minus, Parenthesized(Sum(p, Fin(n), Sum(q, Fin(n), summand)))))))))));
    }

    private static Formula Eigenvalues()
    {
        Formula index = Iota, m = F.Id("M"), h = F.Id("h"), a = F.Id("a"), b = F.Id("b");
        Formula order = Lam(a, Reals(), Lam(b, Reals(), Relation(a, FormulaRelationOperator.LessThanOrEqual, b)));
        Formula sorted = Call("Multiset.sort",
            Call("Multiset.map", Call("Matrix.IsHermitian.eigenvalues", h), Named("Finset.univ.val")), order);
        Formula conditional = Seq(Named("if"), Sp, h, Colon, Sp, Call("Matrix.IsHermitian", m), Sp,
            Named("then"), Sp, sorted, Sp, Named("else"), Sp, Seq(OpenBracket, CloseBracket));
        return Disp(All(index, Named("Type"), Instance(Call("Fintype", index), Instance(Call("DecidableEq", index),
            All(m, MatrixType(index), Equal(Call("eigAsc", m), Parenthesized(conditional)))))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), g = F.Id("G"), s = F.Id("s"), theta = Theta, x = F.Id("x"), k = F.Id("k");
        Formula h = Call("H", g, s, theta);
        Formula odd = Seq(OpenBrace, x, Colon, Sp, Bits(n), Sp, Mid, Sp, Call("Odd", Call("Finset.card", Call("Finset.filter", Lam(k, Fin(n), Equal(App(x, k), D(1))), Named("Finset.univ")))), CloseBrace);
        Formula inclusion = Cast(Named("Subtype.val"), Fn(odd, Bits(n)));
        Formula equality = Equal(Call("List.getD", Call("eigAsc", h), D(1), D(0)),
            Call("List.getD", Call("eigAsc", Call("Matrix.submatrix", h, inclusion, Named("Subtype.val"))), D(0), D(0)));
        return All(n, Nats(), Arrow(Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n),
            All(g, Call("SimpleGraph", Fin(n)), Instance(Call("DecidableRel", Named("G.Adj")),
                Arrow(Call("SimpleGraph.Connected", g), All(s, Reals(),
                    Arrow(Relation(D(0), FormulaRelationOperator.LessThanOrEqual, s),
                        Arrow(Relation(s, FormulaRelationOperator.LessThan, D(1)),
                            All(theta, Fn(Fin(n), Fn(Fin(n), Reals())), equality)))))))));
    }
}
