using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class NegativityReductionInclusionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/abellanetvidalmullerrigatricosanpera2026spectrum");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pure two-qutrit state has the attained negativity bound but fails positive reduction.",
        H("Negativity does not imply positive reduction"),
        Blocks(
            Paragraph(Text(
                "The partial transpose acts on the second factor, and the partial trace over that "
                    + "factor gives the first reduced state. Matrix.PosSemidef means positive "
                    + "semidefinite. The numeral one of matrix type is the identity matrix. "
                    + "The variable chi denotes χ; its casts to ℝ and ℂ are displayed separately. "
                    + "Matrix.kronecker denotes the Kronecker product ⊗ₖ, and SMul.smul denotes "
                    + "scalar multiplication.")),
            Node("negativity", "Negativity from the trace norm", NegativityFormula(),
                "Definition 2, equation (7), defines N(ρ) = (‖ρ^Γ‖₁ − 1)/2. The trace norm "
                    + "is the real part of Tr √(A†A), and Γ transposes the second subsystem. "
                    + "This formula defines negativity on every complex matrix of the indicated "
                    + "size; the density-state conditions appear in the implication below.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The attained-value inclusion", ClaimFormula(),
                "The hypothesis is the attained value N(ρ) = (χ − 1)/2, rather than the "
                    + "sublevel condition N(ρ) ≤ (χ − 1)/2 of Lemma 3. The attained-value "
                    + "hypothesis is stronger, so this universal implication is weaker than its "
                    + "sublevel form. Equation (35) gives RED_χ(X) = Tr(X)1 − X/χ, hence "
                    + "[1 ⊗ RED_χ](ρ) = ρ_A ⊗ 1 − ρ/χ, where ρ_A is the partial trace "
                    + "over the second subsystem. Theorem 7 states that failure of this positivity "
                    + "implies Schmidt number greater than χ. The question in §5.4 also has a non-FS reading, "
                    + "which is the implication displayed here. The FS inclusion, with its "
                    + "additional quantifier over global unitaries, is a separate question.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("negativity-reduction-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The inclusion fails in dimension three"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take ρ = |v⟩⟨v|/18 with v = 4|00⟩ + |11⟩ + |22⟩ and χ = 2. "
                        + "This is a positive semidefinite two-qutrit state of trace one. "
                        + "The trace norm of ρ^Γ is 2, so N(ρ) = 1/2 = (χ − 1)/2. "
                        + "Its reduced state is diag(16, 1, 1)/18. On the test vector "
                        + "|00⟩ + 4|11⟩ + 4|22⟩, the quadratic form of ρ_A ⊗ 1 − ρ/2 "
                        + "has value −4/3. Thus the reduction is not positive semidefinite. "
                        + "Because the negativity bound is attained, the same state also "
                        + "refutes the sublevel implication. This does not settle the FS inclusion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("abellanet-vidal-muller-rigat-rico-sanpera-2026-negativity-reduction-inclusion"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("negativity-reduction-" + declaration),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula NegativityFormula() => BipartiteBinders(All(Rho, JointMatrix(),
        Equal(Typed(LocalCall("negativity", Rho), Reals()),
            Quotient(Subtract(Call("D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm",
                Call("D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.partialTranspose", Rho)),
                D(1)), D(2)))));

    private static Formula ClaimFormula() => Equivalence(Typed(Local("claim"), V("Prop")),
        BipartiteBinders(All(Rho, JointMatrix(), All(V("chi"), Naturals(),
            Imp(Call("Matrix.PosSemidef", Rho),
                Imp(Equal(Call("Matrix.trace", Rho), D(1)),
                    Imp(LE(D(1), V("chi")),
                        Imp(LE(V("chi"), Call("Fintype.card", V("a"))),
                            Imp(LE(V("chi"), Call("Fintype.card", V("b"))),
                                Imp(Equal(LocalCall("negativity", Rho),
                                        Quotient(Subtract(Typed(V("chi"), Reals()), D(1)), D(2))),
                                    Call("Matrix.PosSemidef", Reduction())))))))))));

    private static Formula Reduction() => Subtract(
        Call("Matrix.kronecker",
            Call("D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight", Rho),
            Typed(D(1), Call("Matrix", V("b"), V("b"), Complexes()))),
        Call("SMul.smul", new Formula.Power(Typed(V("chi"), Complexes()), new Formula.Negate(D(1))), Rho));

    private static Formula BipartiteBinders(Formula body) => Seq(Forall, Sp,
        Typed(V("a"), V("Type")), Sp, Typed(V("b"), V("Type")), Sp,
        Instance("Fintype", "a"), Sp, Instance("DecidableEq", "a"), Sp,
        Instance("Fintype", "b"), Sp, Instance("DecidableEq", "b"), Comma, Sp,
        Parenthesized(body));
    private static Formula Instance(string name, string type) =>
        Seq(OpenBracket, Call(name, V(type)), CloseBracket);
    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(
        "D5.S3.QuantumBounds.NegativityReductionInclusionRefutation." + name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Qualified(name), [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => new Formula.Apply(Local(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula JointMatrix() => Call("Matrix",
        Parenthesized(Seq(V("a"), Sp, Times, Sp, V("b"))),
        Parenthesized(Seq(V("a"), Sp, Times, Sp, V("b"))), Complexes());
    private static Formula Quotient(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
