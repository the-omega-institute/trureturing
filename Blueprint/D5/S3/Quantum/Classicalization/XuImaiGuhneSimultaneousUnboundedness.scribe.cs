using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Classicalization;

internal sealed class XuImaiGuhneSimultaneousUnboundednessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/xuimaiguhne2023classicalization");
    private const string Question = "Section V.B, page 5: “Inspired by those two examples, an interesting question arises whether there exist entanglement measures E and states ρ_ABC such that both Δ_E(ρ_ABC) and Δ̃_E(ρ_ABC) − Δ_E(ρ_ABC) can be arbitrarily large in the sense that they are not limited by the size of C, even if C is only a qubit. We leave this question for further research.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both classicalization gaps for tripartite negativity are unbounded with a qubit measured party.",
        H("Two unbounded entanglement gaps with one qubit"), Blocks(
            Node("tripartite", "tripartiteNegativity", TripartiteDefinition(), AssessedProvenance.FromLiterature(Source),
                "Equation (4), page 3: “N_ABC(ρ_ABC) = N_{AB|C} + N_{BC|A} + N_{AC|B}”, where N_{X|Y} “is the negativity for a bipartition X|Y with eigenvalues λ_i of the partial transposed state ρ^{T_Y} with respect to the subsystem Y”. The three regroupings transpose C, A and B respectively. The bipartite negativity is (traceNorm(partialTranspose ρ) − 1)/2; its sign is the standard positive negativity, as in the source's numerical values."),
            Node("branch", "branch", BranchDefinition(), AssessedProvenance.FromLiterature(Source),
                "Equation (1), page 2: “p_i = tr(ρ_ABC m_i), σ_i = tr_C(ρ_ABC m_i)/p_i”. The branch is the unnormalized matrix p_i σ_i, so it also covers zero-probability outcomes without division."),
            Node("classicalize", "classicalize", ClassicalizeDefinition(), AssessedProvenance.FromLiterature(Source),
                "Equation (1), page 2: “Φ_C(ρ_ABC) = Σ_i p_i σ_i ⊗ τ_i, where p_i = tr(ρ_ABC m_i), σ_i = tr_C(ρ_ABC m_i)/p_i and τ_i is the register state related to the outcome i”. The outcome type is any finite type, and the prepared register has carrier E."),
            Node("delta", "delta", DeltaDefinition(), AssessedProvenance.FromLiterature(Source),
                "Equation (2), page 2: “Δ_E(ρ_ABC) = min_{Φ_C ∈ N_C} {E[ρ_ABC] − E[Φ_C(ρ_ABC)]}”. Here E is tripartiteNegativity. Effects are positive semidefinite and sum to the identity; each register matrix is positive semidefinite with trace one. The infimum ranges over every finite outcome count and every finite register dimension. For the constructed family the infimum is attained by a two-outcome measurement with two orthogonal qubit states."),
            Node("delta-tilde", "deltaTilde", DeltaTildeDefinition(), AssessedProvenance.FromLiterature(Source),
                "Equation (9), page 3: “Δ̃_E(ρ_ABC) = E[ρ_ABC] − E[ρ_AB ⊗ |0⟩⟨0|], with ρ_AB = tr_C(ρ_ABC)”. The register is Fin 2 and its zero basis vector supplies the rank-one flag."),
            Node("claim", "claim", Eqn(X("claim"), Parenthesized(ClaimBody())), AssessedProvenance.FromLiterature(Source),
                Question + " The proposition answers the question with the fixed measure tripartiteNegativity. A and B have arbitrary finite dimensions, C has dimension exactly two, and a single state exceeds the same real threshold in both gaps."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + ".result"),
                H("Simultaneous unboundedness"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Tensor a normalized three-qubit W state with a maximally entangled state of local dimension d on A and B. Rank-one refinement of any qubit POVM gives branch partial-transpose norms (4|α|²+|β|²)/3, whose sum is 5/3. The triangle inequality bounds the output entanglement by 5d/3−1, attained with computational-basis measurement and orthogonal flags. The output-register cut has zero negativity. The two gaps equal [2d(√2−1)+√2]/3 and d(3−√5)/3. Both coefficients of d are positive; choosing d sufficiently large proves the displayed proposition."))), DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string id, string name, Formula formula,
        AssessedProvenance provenance, string text) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Owner + "." + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula TripartiteDefinition()
    {
        var rho = X("rho");
        var assoc = App(Q("Equiv", "prodAssoc"), X("A"), X("B"), X("C"));
        var comm = App(Q("Equiv", "prodComm"), Product(X("B"), X("C")), X("A"));
        var swap = Lambda("p", Product(Product(X("A"), X("C")), X("B")),
            Tuple(Proj(Proj(X("p"), 1), 1), Proj(X("p"), 2), Proj(Proj(X("p"), 1), 2)));
        return ThreeCarriers(All("rho", Matrix(Triple(X("A"), X("B"), X("C"))),
            Eqn(Call("tripartiteNegativity", rho), Add(Add(
                Call("negativity", Submatrix(rho, assoc)), Call("negativity", Submatrix(rho, comm))),
                Call("negativity", Submatrix(rho, swap))))));
    }

    private static Formula BranchDefinition() => Types(["A", "B", "C"],
        Instance("Fintype", X("C"), All("rho", Matrix(Triple(X("A"), X("B"), X("C"))),
            All("m", Matrix(X("C")), Eqn(Call("branch", X("rho"), X("m")),
                Parenthesized(Lambda("p", Product(X("A"), X("B")), Lambda("q", Product(X("A"), X("B")),
                    Summation("c", X("C"), Summation("z", X("C"), Mul(
                        App(X("rho"), Tuple(Proj(X("p"), 1), Proj(X("p"), 2), X("c")),
                            Tuple(Proj(X("q"), 1), Proj(X("q"), 2), X("z"))),
                        App(X("m"), X("z"), X("c")))))))))))));

    private static Formula ClassicalizeDefinition() => Types(["A", "B", "C", "I", "E"],
        Instance("Fintype", X("C"), Instance("Fintype", X("I"),
            All("rho", Matrix(Triple(X("A"), X("B"), X("C"))),
                All("m", Arrow(X("I"), Matrix(X("C"))), All("tau", Arrow(X("I"), Matrix(X("E"))),
                    Eqn(Call("classicalize", X("rho"), X("m"), X("tau")), Parenthesized(
                        Lambda("p", Triple(X("A"), X("B"), X("E")), Lambda("q", Triple(X("A"), X("B"), X("E")),
                            Summation("i", X("I"), Mul(
                                App(Call("branch", X("rho"), App(X("m"), X("i"))),
                                    Tuple(Proj(X("p"), 1), Proj(Proj(X("p"), 2), 1)),
                                    Tuple(Proj(X("q"), 1), Proj(Proj(X("q"), 2), 1))),
                                App(X("tau"), X("i"), Proj(Proj(X("p"), 2), 2), Proj(Proj(X("q"), 2), 2))))))))))))));

    private static Formula DeltaDefinition()
    {
        var effects = Arrow(Fin(X("k")), Matrix(X("C")));
        var registers = Arrow(Fin(X("k")), Matrix(Fin(X("e"))));
        var valid = And(And(All("i", Fin(X("k")), Property(App(X("m"), X("i")), "PosSemidef")),
            Eqn(Summation("i", Fin(X("k")), App(X("m"), X("i"))), D(1))),
            And(All("i", Fin(X("k")), State(App(X("tau"), X("i")))),
                Eqn(X("x"), Subtract(Call("tripartiteNegativity", X("rho")),
                    Call("tripartiteNegativity", Call("classicalize", X("rho"), X("m"), X("tau")))))));
        var values = SetBuilder("x", Real(), Ex("k", Nat(), Ex("e", Nat(), Ex("m", effects, Ex("tau", registers, valid)))));
        return ThreeCarriers(All("rho", Matrix(Triple(X("A"), X("B"), X("C"))),
            Eqn(Call("delta", X("rho")), Call("sInf", values))));
    }

    private static Formula DeltaTildeDefinition()
    {
        var carrier = Triple(X("A"), X("B"), Fin(D(2)));
        var flag = If(And(Eqn(Proj(Proj(X("p"), 2), 2), D(0)), Eqn(Proj(Proj(X("q"), 2), 2), D(0))), D(1), D(0));
        var decoded = Lambda("p", carrier, Lambda("q", carrier, Mul(
            App(Call("branch", X("rho"), D(1)),
                Tuple(Proj(X("p"), 1), Proj(Proj(X("p"), 2), 1)),
                Tuple(Proj(X("q"), 1), Proj(Proj(X("q"), 2), 1))), Parenthesized(flag))));
        return Types(["A", "B"], Finite("A", Finite("B", All("rho", Matrix(carrier),
            Eqn(Call("deltaTilde", X("rho")), Subtract(Call("tripartiteNegativity", X("rho")),
                Call("tripartiteNegativity", Parenthesized(decoded))))))));
    }

    private static Formula ClaimBody() => All("M", Real(), Ex("a", Nat(), Ex("b", Nat(),
        Ex("rho", Matrix(Triple(Fin(X("a")), Fin(X("b")), Fin(D(2)))),
            And(State(X("rho")), And(Less(X("M"), Call("delta", X("rho"))),
                Less(X("M"), Subtract(Call("deltaTilde", X("rho")), Call("delta", X("rho"))))))))));

    private static Formula ThreeCarriers(Formula body) => Types(["A", "B", "C"], Finite("A", Finite("B", Finite("C", body))));
    private static Formula Types(string[] names, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--) body = All(names[i], X("Type"), body);
        return body;
    }
    private static Formula Finite(string name, Formula body) => Instance("Fintype", X(name), Instance("DecidableEq", X(name), body));
    private static Formula Instance(string name, Formula arg, Formula body) => Seq(OpenBracket, Call(name, arg), CloseBracket, Sp, Comma, Sp, body);
    private static Formula State(Formula rho) => And(Property(rho, "PosSemidef"), Eqn(Property(rho, "trace"), D(1)));
    private static Formula Matrix(Formula carrier) => Call("Matrix", carrier, carrier, Complex());
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Triple(Formula a, Formula b, Formula c) => Product(a, Product(b, c));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Tuple(params Formula[] values)
    {
        var items = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(values[i]);
        }
        return Parenthesized(new Formula.LatexSequence([.. items]));
    }
    private static Formula Proj(Formula value, byte index) => Seq(Parenthesized(value), Dot, D(index));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(X(name), args);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula type, Formula body) => Seq(X("fun"), Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Summation(string name, Formula type, Formula body) => Seq(Sum, Sp, X(name), Sp, Colon, Sp, type, Sp, Comma, Sp, body);
    private static Formula SetBuilder(string name, Formula type, Formula body) => Seq(OpenBrace, X(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Property(Formula a, string name) => Seq(Parenthesized(a), Dot, Operatorname, Grp(X(name)));
    private static Formula Submatrix(Formula rho, Formula e) => App(Q("Matrix", "submatrix"), rho, Parenthesized(e), Parenthesized(e));
    private static Formula If(Formula condition, Formula yes, Formula no) => Seq(X("if"), Sp, Parenthesized(condition), Sp, X("then"), Sp, yes, Sp, X("else"), Sp, no);
}
