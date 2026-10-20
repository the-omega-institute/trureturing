using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class QutritCollectiveDephasingInvariantNegativityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/ali2019qutritfreezing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonstationary two-qutrit density matrix has constant positive negativity under Ali's collective dephasing.",
        H("Collective dephasing can preserve negativity while changing the state"),
        Blocks(
            Paragraph(Text(
                "The computational basis is ordered (0,0), (0,1), (0,2), (1,0), (1,1), "
                    + "(1,2), (2,0), (2,1), (2,2). Each local index belongs to Fin 3. "
                    + "All matrices below act on ℂ³ ⊗ ℂ³, and H denotes the conjugate transpose. "
                    + "Write γ(Γ,t) for gammaFactor(Γ,t), D₁ for kraus1, D₂ for kraus2, "
                    + "D₃ for kraus3, Φ for evolve, and N for negativity. Real diagonal entries "
                    + "are embedded in ℂ. The definitions allow all real Γ and t; the "
                    + "dephasing claim imposes Γ > 0 and t ≥ 0. The real square root is "
                    + "nonnegative on nonnegative inputs and is zero on nonpositive inputs.")),
            Node("gamma", "The damping factor", GammaFormula(),
                "Section II defines γ = exp(−Γt/2).",
                "gammaFactor"),
            Node("omega1", "The first auxiliary coefficient", OmegaFormula("omega1",
                Root(Sub(D(1), GammaSquared()))),
                "Section II defines ω₁ = √(1−γ²), using the nonnegative real square root.",
                "omega1"),
            Node("omega2", "The second auxiliary coefficient", OmegaFormula("omega2",
                Mul(new Formula.Negate(GammaSquared()), Root(Sub(D(1), GammaSquared())))),
                "Section II defines ω₂ = −γ²√(1−γ²).",
                "omega2"),
            Node("omega3", "The third auxiliary coefficient", OmegaFormula("omega3",
                Mul(Sub(D(1), GammaSquared()), Root(Add(D(1), GammaSquared())))),
                "Section II defines ω₃ = (1−γ²)√(1+γ²).",
                "omega3"),
            Node("kraus1", "The first diagonal Kraus operator", KrausFormula("kraus1",
                G, D(1), D(1), D(1), G, D(1), D(1), D(1), G),
                "The entries of D₁ follow the stated computational basis order. The factor γ "
                    + "occurs exactly at (0,0), (1,1), and (2,2).",
                "kraus1"),
            Node("kraus2", "The second diagonal Kraus operator", KrausFormula("kraus2",
                Coefficient("omega1"), D(0), D(0), D(0), Coefficient("omega2"),
                D(0), D(0), D(0), Coefficient("omega2")),
                "In the same basis order, D₂ has entries ω₁ at (0,0), ω₂ at (1,1) and (2,2), "
                    + "and zero elsewhere.",
                "kraus2"),
            Node("kraus3", "The third diagonal Kraus operator", KrausFormula("kraus3",
                D(0), D(0), D(0), D(0), Coefficient("omega3"),
                D(0), D(0), D(0), Coefficient("omega3")),
                "In the same basis order, D₃ has entries ω₃ at (1,1) and (2,2), and zero elsewhere.",
                "kraus3"),
            Node("evolve", "Collective dephasing evolution", EvolutionFormula(),
                "Equation (3) gives ΦΓ,t(ρ) = Σₖ DₖᴴρDₖ for k = 1, 2, 3. "
                    + "The displayed three-term sum fixes the order of the adjoints and products.",
                "evolve"),
            Describe.Lean(
                DescribeId.Create("ali-qutrit-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Constant positive negativity would imply stationarity"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Section I says that time-invariant entanglement allows the quantum state "
                            + "to change while its entanglement remains constant throughout the dynamics. "
                            + "Section V conjectures: \"under current dynamics, this feature of "
                            + "time-invariant entanglement may not exist for qutrit-qutrit systems.\" "
                            + "With the negativity used in Section III as the entanglement measure, "
                            + "claim states that every positive semidefinite unit-trace initial matrix "
                            + "with constant strictly positive negativity is stationary for all t ≥ 0. "
                            + "It quantifies over every Γ > 0 and every such initial matrix.")),
                    Paragraph(Text(
                        "Negativity is N(ρ) = (‖ρ^{T_B}‖₁−1)/2. The partial transpose exchanges "
                            + "the second subsystem indices. The trace norm is Tr √(AᴴA); its "
                            + "real part is explicit below, matching the real-valued convention. "
                            + "These formulas apply to every complex matrix, with no density "
                            + "hypothesis in the definitions themselves.")),
                    Display(NegativityFormula()),
                    Display(PartialTransposeFormula()),
                    Display(TraceNormFormula())),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ali-qutrit-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A nonstationary state with negativity one quarter"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take Γ = 2 and ρ₀ = ¾|φ⟩⟨φ| + ¼|χ⟩⟨χ|, where "
                            + "φ = (|01⟩+|10⟩)/√2 and χ = (|00⟩+|11⟩)/√2. "
                            + "The two normalized vectors give ρ₀ ⪰ 0 and Tr ρ₀ = 1. "
                            + "For t ≥ 0 put g = γ(2,t) = exp(−t), so 0 < g ≤ 1, "
                            + "and set u₊ = |00⟩+|11⟩, u₋ = |00⟩−|11⟩, "
                            + "w₊ = |01⟩+|10⟩, w₋ = |01⟩−|10⟩.")),
                    Paragraph(Text(
                        "The evolved matrix is Φ₂,t(ρ₀) = (3/8)w₊w₊ᴴ "
                            + "+ ((1+g⁴)/16)u₊u₊ᴴ + ((1−g⁴)/16)u₋u₋ᴴ. "
                            + "Indeed γ²+ω₁² = 1, γ²+ω₂²+ω₃² = 1, and γ²+ω₁ω₂ = γ⁴. "
                            + "Thus only the (00,11) and (11,00) entries change, from 1/8 to g⁴/8.")),
                    Paragraph(Text(
                        "Its partial transpose is A−B, where A = (1/4)u₊u₊ᴴ "
                            + "+ ((3+g⁴)/16)w₊w₊ᴴ + ((3−g⁴)/16)w₋w₋ᴴ "
                            + "and B = (1/8)u₋u₋ᴴ. All coefficients are nonnegative, "
                            + "so A and B are positive semidefinite. Orthogonality of u₋ to "
                            + "u₊, w₊, and w₋ gives AB = 0. Their traces are Tr A = 5/4 "
                            + "and Tr B = 1/4; hence Tr A + Tr B = 3/2. The trace norm "
                            + "of A−B is therefore 3/2, and N(Φ₂,t(ρ₀)) = N(ρ₀) = 1/4 "
                            + "for every t ≥ 0.")),
                    Paragraph(Text(
                        "At t = 1 the (00,11) entry is exp(−4)/8 < 1/8, "
                            + "so Φ₂,1(ρ₀) ≠ ρ₀. This contradicts claim. "
                            + "The construction uses a two-qubit corner of the two-qutrit space: "
                            + "a stationary Bell component accompanies a changing component "
                            + "without changing the negative part of the partial transpose. "
                            + "It supplies time-invariant positive negativity for the dynamics "
                            + "specified by Ali."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ali-2018-qutrit-collective-dephasing-invariant-negativity-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration) => Describe.Lean(
            DescribeId.Create("ali-qutrit-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula GammaFormula() => Parameters(Equal(Coefficient("gammaFactor"),
        Call("exp", new Formula.Negate(Div(Mul(Gamma, V("t")), D(2))))));

    private static Formula OmegaFormula(string name, Formula value) =>
        Parameters(Equal(Coefficient(name), value));

    private static Formula KrausFormula(string name, params Formula[] entries) =>
        Parameters(Equal(Typed(Coefficient(name), JointMatrix()), Call("diag", entries)));

    private static Formula EvolutionFormula()
    {
        var r = V("r");
        Formula Term(Formula op) => Mul(Mul(Adjoint(op), r), op);
        var sum = Seq(Sum, Underscore, Grp(V("k"), Eq, D(1)), Caret, Grp(D(3)), Sp,
            Term(new Formula.Apply(new Formula.Subscript(V("D"), V("k")), [Gamma, V("t")])));
        return Parameters(All(r, JointMatrix(), new Formula.RelationChain(FormulaRelationOperator.Equal,
            [Evolution(Gamma, V("t"), r), sum,
                Add(Add(Term(Coefficient("kraus1")), Term(Coefficient("kraus2"))),
                    Term(Coefficient("kraus3")))])));
    }

    private static Formula ClaimFormula()
    {
        var r = V("r");
        var constant = All(V("t"), Reals(), Imp(Leq(D(0), V("t")),
            Equal(Negativity(Evolution(Gamma, V("t"), r)), Negativity(r))));
        var stationary = All(V("t"), Reals(), Imp(Leq(D(0), V("t")),
            Equal(Evolution(Gamma, V("t"), r), r)));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff,
            All(Gamma, Reals(), Imp(Less(D(0), Gamma), All(r, JointMatrix(),
                Imp(Call("PosSemidef", r), Imp(Equal(Call("Tr", r), D(1)),
                    Imp(Less(D(0), Negativity(r)), Imp(constant, stationary))))))));
    }

    private static Formula NegativityFormula() => All(V("r"), JointMatrix(),
        Equal(Negativity(V("r")), Div(Sub(NormOne(PartialTranspose(V("r"))), D(1)), D(2))));

    private static Formula PartialTransposeFormula()
    {
        var equation = Equal(Entry(PartialTranspose(V("r")), Pair(V("i"), V("j")), Pair(V("k"), V("l"))),
            Entry(V("r"), Pair(V("i"), V("l")), Pair(V("k"), V("j"))));
        foreach (var index in new[] { "l", "k", "j", "i" }) equation = All(V(index), FinThree(), equation);
        return All(V("r"), JointMatrix(), equation);
    }

    private static Formula TraceNormFormula() => All(V("M"), JointMatrix(), Equal(NormOne(V("M")),
        Call("Re", Call("Tr", Root(Mul(Adjoint(V("M")), V("M")))))));

    private static Formula Parameters(Formula body) => All(Gamma, Reals(), All(V("t"), Reals(), body));
    private static Formula Coefficient(string name) => Call(name, Gamma, V("t"));
    private static Formula G => Coefficient("gammaFactor");
    private static Formula GammaSquared() => new Formula.Power(G, D(2));
    private static Formula Negativity(Formula matrix) => Call("negativity", matrix);
    private static Formula Evolution(Formula rate, Formula time, Formula matrix) => Call("evolve", rate, time, matrix);
    private static Formula PartialTranspose(Formula matrix) =>
        new Formula.Power(matrix, new Formula.Subscript(V("T"), V("B")));
    private static Formula NormOne(Formula matrix) => new Formula.Subscript(new Formula.Norm(matrix), D(1));
    private static Formula Adjoint(Formula matrix) => new Formula.Power(Parenthesized(matrix), V("H"));
    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        new Formula.Subscript(Parenthesized(matrix), Seq(row, Comma, column));
    private static Formula Pair(Formula first, Formula second) => Parenthesized(Seq(first, Comma, second));
    private static Formula JointMatrix() => Call("Matrix", PairType(), PairType(), Complexes());
    private static Formula PairType() => Parenthesized(Seq(FinThree(), Times, FinThree()));
    private static Formula FinThree() => Call("Fin", D(3));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static DocumentBlock Display(Formula formula) => new DocumentBlock.DisplayFormula(Disp(formula));
}
