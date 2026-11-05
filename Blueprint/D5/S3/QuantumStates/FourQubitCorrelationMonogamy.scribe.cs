using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class FourQubitCorrelationMonogamyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumStates/FourQubitCorrelationMonogamy.";
    private const string PauliOwner = "D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/chengmilnehallwiseman2016volume");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The twenty-seven squared two-body Pauli correlations of a normalized four-qubit vector sum to at most three.",
        H("Four-qubit correlation monogamy"),
        Blocks(
            Paragraph(Text(
                "The qubits are ordered A, B, C, D, with positions 0, 1, 2, 3. "
                + "The target index X = 0, 1, 2 denotes B, C, D, respectively, and each Pauli index "
                + "i or j = 0, 1, 2 denotes the x, y, z spin direction. The amplitude vector ψ "
                + "is indexed by functions from Fin 4 to Fin 2, the sixteen computational basis states.")),
            Describe.Lean(
                DescribeId.Create("two-body-word"), DeclarationHandle.Create(Prefix + "twoBodyWord"),
                H("A two-body Pauli word"), StatementSource.FromAuthor(Disp(TwoBodyWordFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The word places Pauli i on A and Pauli j on the target X, with the identity "
                        + "on the other two qubits. Fin.succ sends X to its position among B, C, D. "
                        + "The ordered vector ![Pauli.X, Pauli.Y, Pauli.Z] supplies the three spin labels from "),
                        Ref(PauliOwner + "Pauli"), Text(
                        ". These are the two-body observables in the source's correlation entries "
                        + "Tᵢⱼ, defined in arXiv:1606.02390v2, finalversion.tex, lines 123–133."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("correlation"), DeclarationHandle.Create(Prefix + "correlation"),
                H("A reduced-state correlation entry"), StatementSource.FromAuthor(Disp(CorrelationFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The matrix "),
                        Ref("D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity"),
                        Text(" is the outer product ψψ†, and "), Ref(PauliOwner + "wordOp"),
                        Text(
                            " turns the word into its four-qubit tensor-product observable. "
                            + "The correlation is the real part of the trace of their product. "
                            + "For normalized ψ this is Tᵢⱼ of the AX reduced state: the identity factors "
                            + "on the two remaining qubits give the same expectation before or after "
                            + "the partial trace. This expresses the source's definition in "
                            + "finalversion.tex, lines 129–133, on the full four-qubit space. "
                            + "The displayed definition also applies to unnormalized vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The conjectured sum of squared correlations"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Local("claim"), Qualified("Prop")),
                    Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The source conjectures equation (36) for all pure four-qubit states "
                    + "in arXiv:1606.02390v2, finalversion.tex, lines 395–399. Its three terms "
                    + "are the squared Frobenius norms of the AB, AC and AD correlation matrices. "
                    + "Here each norm is the sum of the nine squared real correlation entries, "
                    + "and purity is expressed by a vector whose conjugate dot product with itself is one. "
                    + "The source states this as a conjecture supported by numerical observations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The correlation sum is at most three"),
                StatementSource.FromAuthor(Disp(ClaimProposition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For each k in Fin 3, index nine words by u in Fin 3 × Fin 3, taking "
                        + "the target u.1, the Pauli direction k + u.1 on A, and the direction u.2 "
                        + "on the target. Addition here is modulo three. For distinct u and v, "
                        + "the product of the four letter commutation signs is −1. When the targets "
                        + "agree, the target letters differ; when the targets differ, the letters "
                        + "on A differ. In either case exactly one position contributes a negative sign. "
                        + "The Hermitian Pauli-word matrices square to the identity, and the signed "
                        + "word commutation law makes each of the three families pairwise anticommuting.")),
                    Paragraph(Text(
                        "For a finite family P of Hermitian involutions with these anticommutation "
                        + "relations, let ρ be any density state and set a i = expectation ρ (P i), "
                        + "H = ∑ i, (a i : ℂ) • P i and s = ∑ i, (a i)². The real coefficients "
                        + "make H Hermitian. Apply "),
                        Ref("D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.cliffordLinear_anticommutator"),
                        Text(
                            " to the two identical coefficient families i ↦ (a i : ℂ). "
                            + "After cancelling the nonzero complex scalar 2, it gives "
                            + "H² = (s : ℂ) • I.")),
                    Paragraph(Text("Expanding "),
                        Ref("D5/S3/Quantum/Information/CovarianceSumBound.expectation"),
                        Text(
                            " through the finite sum and the real scalar coefficients gives "
                            + "expectation ρ H = s. The square identity and trace ρ = 1 give "
                            + "expectation ρ (H²) = s. Hence "),
                        Ref("D5/S3/Quantum/Information/CovarianceSumBound.variance_nonneg"),
                        Text(
                            " yields 0 ≤ s − s². Since 0 ≤ (s − 1)² ≤ 1 − s, it follows that s ≤ 1.")),
                    Paragraph(Text(
                        "Applying this bound to each nine-element family bounds its squared "
                        + "expectations by one. To sum the families, first exchange the i and j sums. "
                        + "For each fixed X and j, the bijection k ↦ k + X of Fin 3 replaces the "
                        + "i sum by the k sum. Exchanging the remaining finite sums then partitions "
                        + "all twenty-seven terms into the three families. Summing their bounds gives "
                        + "∑ k : Fin 3, 1 = 3 for every density state on the four-qubit space.")),
                    Paragraph(Text("For a normalized vector ψ, "),
                        Ref("D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.pureDensityState"),
                        Text(
                            " supplies the density state with matrix ψψ†. Its expectations of the "
                            + "two-body words are exactly correlation ψ X i j. Substituting this density "
                            + "state into the preceding bound proves the displayed proposition for every "
                            + "normalized pure four-qubit vector."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cheng-milne-hall-wiseman-2016-four-qubit-correlation-monogamy"),
                    ResolutionKind.Proved)))));

    private static Formula TwoBodyWordFormula()
    {
        Formula word = At(Qualified("ite"), Equal(X("q"), Typed(D(0), FinOf(4))),
            At(PauliVector(), X("i")),
            At(Qualified("ite"), Equal(X("q"), At(Qualified("Fin", "succ"), X("X"))),
                At(PauliVector(), X("j")), Pauli("I")));
        return All("X", FinOf(3), All("i", FinOf(3), All("j", FinOf(3),
            Equal(Typed(LocalCall("twoBodyWord", X("X"), X("i"), X("j")),
                    Arrow(FinOf(4), Pauli())), LambdaOf("q", FinOf(4), word)))));
    }

    private static Formula CorrelationFormula()
    {
        Formula density = At(Qualified("D5", "S3", "Quantum", "PureState", "PureStateHandshake", "rankOneDensity"),
            X("ψ"));
        Formula observable = At(Qualified("D5", "S3", "Quantum", "Information",
            "StabilizerPairLocalUnitaryInequivalence", "wordOp"),
            LocalCall("twoBodyWord", X("X"), X("i"), X("j")));
        Formula value = At(Qualified("Complex", "re"),
            At(Qualified("Matrix", "trace"), Multiply(density, observable)));
        return All("ψ", StateType(), All("X", FinOf(3), All("i", FinOf(3), All("j", FinOf(3),
            Equal(Typed(LocalCall("correlation", X("ψ"), X("X"), X("i"), X("j")), Reals()), value)))));
    }

    private static Formula ClaimProposition()
    {
        Formula normalization = Equal(At(Qualified("dotProduct"), At(Qualified("star"), X("ψ")), X("ψ")),
            Typed(D(1), Complexes()));
        Formula total = SumOver("X", FinOf(3), SumOver("i", FinOf(3), SumOver("j", FinOf(3),
            new Formula.Power(Parenthesized(LocalCall("correlation", X("ψ"), X("X"), X("i"), X("j"))), D(2)))));
        return All("ψ", StateType(), Arrow(normalization,
            new Formula.Relation(total, FormulaRelationOperator.LessThanOrEqual, Typed(D(3), Reals()))));
    }

    private static Formula PauliVector() => Seq(Bang, OpenBracket, Pauli("X"), Comma, Sp,
        Pauli("Y"), Comma, Sp, Pauli("Z"), CloseBracket);
    private static Formula Pauli(params string[] suffix) => Qualified(["D5", "S3", "Quantum", "Information",
        "StabilizerPairLocalUnitaryInequivalence", "Pauli", .. suffix]);
    private static Formula StateType() => Arrow(Arrow(FinOf(4), FinOf(2)), Complexes());
    private static Formula Local(string name) => Qualified("D5", "S3", "QuantumStates", "FourQubitCorrelationMonogamy", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name == "ψ" ? new Formula.Psi() : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(byte n) => At(Qualified("Fin"), D(n));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
}
