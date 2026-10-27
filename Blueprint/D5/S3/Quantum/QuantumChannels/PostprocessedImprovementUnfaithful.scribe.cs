using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class PostprocessedImprovementUnfaithfulDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/masinitheurerplenio2021interferometry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every biased prior admits a coherence-creating qubit channel with zero post-processed improvement.",
        H("Biased post-processed improvements are not faithful"),
        Blocks(
            Paragraph(Text(
                "Matrices have complex entries. MatrixMap(Fin a, Fin b, ℂ) is the space of complex linear maps "
                    + "from a by a matrices to b by b matrices. IsChannel means completely positive and "
                    + "trace preserving, traceNorm is the matrix trace norm, and LinearMap.comp applies "
                    + "its second argument first. The prior l is real, and the complementary prior is 1 − l.")),
            Node("dephase", "Full dephasing", "dephase", DephaseFormula(),
                "Full dephasing extracts the diagonal of a matrix and puts it back into a diagonal matrix. "
                    + "It removes precisely the off-diagonal entries in the coordinate basis. "
                    + "This is the operation Δ in Section II A of Masini, Theurer and Plenio "
                    + "(arXiv:2102.04863v2, TeX lines 111–115). The definition permits every natural dimension n."),
            Node("is-mio", "Maximally incoherent operations", "IsMIO", MioFormula(),
                "A maximally incoherent operation is a channel whose output is diagonal whenever its input "
                    + "has been dephased. The identity is required for every complex input matrix x, "
                    + "and includes both the channel condition and preservation of diagonality. "
                    + "It restates ΨΔ = ΔΨΔ from Section II A (TeX lines 132–134)."),
            Node("phase-channel", "The diagonal phase channel", "phaseChannel", PhaseFormula(),
                "For a real phase function φ on Fin m, conjugate by the diagonal matrix with entries "
                    + "exp(iφ(i)). MatrixMap.conj sends a matrix A to UAU† for the displayed diagonal U. "
                    + "The inclusion Complex.ofReal places each real phase in ℂ before multiplication "
                    + "by Complex.I and exponentiation. This is Λ in Section III (TeX lines 171–175)."),
            Node("induced-trace-norm", "The induced trace norm", "inducedTraceNorm", NormFormula(),
                "Take the real supremum of the trace norms of f(x) over the full complex matrix unit ball "
                    + "traceNorm(x) ≤ 1. The inputs are arbitrary complex matrices, without a positivity "
                    + "or Hermiticity restriction. This is the induced trace norm used in Section III A "
                    + "(TeX line 202). The definition applies to every complex linear map f and all natural "
                    + "input and output dimensions; sSup is the total real supremum operation."),
            Node("post-improvement", "The optimized post-processed improvement", "postImprovement", ImprovementFormula(),
                "For θ from dimension a to dimension b, optimize the induced trace norm over all maximally "
                    + "incoherent maps ψ from dimension b to the phase dimension m. First dephase, then apply θ, "
                    + "then ψ, and finally the weighted difference between the identity and the phase channel. "
                    + "Subtract the prior-only advantage |l − (1 − l)|. This restates Equation (14) "
                    + "(TeX line 273), using a real supremum in place of the maximum. "
                    + "Both weights are explicitly included in ℂ, with 1 − l formed in ℝ before inclusion. "
                    + "The definition itself allows arbitrary natural dimensions and real l; the theorem "
                    + "imposes the probability and nonempty-output conditions it uses."),
            Describe.Lean(
                DescribeId.Create("mtp-postprocessed-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A coherent qubit channel invisible to every biased game"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First fix a phase function φ and put U = diag(exp(iφ(i))). Each diagonal entry "
                            + "has unit modulus. Computing the entries of UAU† shows that the phase channel "
                            + "preserves trace, preserves positive semidefiniteness, and fixes every diagonal matrix.")),
                    Paragraph(Text(
                        "Suppose 0 ≤ l ≤ 1, d is diagonal, and d + e and d − e are positive semidefinite. "
                            + "Set f = l e − (1 − l)UeU†. Then d + f is the sum "
                            + "l(d + e) + (1 − l)U(d − e)U†, and d − f is "
                            + "l(d − e) + (1 − l)U(d + e)U†. Nonnegative scalar multiplication, addition "
                            + "and unitary conjugation preserve positivity, so both d + f and d − f are positive semidefinite.")),
                    Paragraph(Text(
                        "Assume also d ≥ 0, tr(d) = 1, tr(e) = 0 and 0 ≤ t ≤ |2l − 1|. "
                            + "Trace preservation gives tr(f) = 0, so H = (2l − 1)d + t f has trace 2l − 1. "
                            + "When 2l − 1 ≥ 0, write H = (2l − 1 − t)d + t(d + f), a positive semidefinite sum. "
                            + "When 2l − 1 ≤ 0, write −H = (−(2l − 1) − t)d + t(d − f), also positive semidefinite. "
                            + "The trace norm of a positive semidefinite matrix equals its trace, and negation "
                            + "does not change the trace norm. Thus traceNorm(H) = |2l − 1| in both cases.")),
                    Paragraph(Text(
                        "For qubits let d₀ = I₂/2 and e₀ = X/2, where X has zero diagonal and both "
                            + "off-diagonal entries equal to one. For s equal to 1 or −1, d₀ + s e₀ is "
                            + "one half of vv† with v = (1,s), hence is positive semidefinite. "
                            + "For any positive semidefinite ρ with trace one, the map A ↦ tr(A)ρ is a channel: "
                            + "its Choi matrix is ρ ⊗ I, which is positive semidefinite, and its output trace is tr(A).")),
                    Paragraph(Text(
                        "Now take any maximally incoherent ψ from the qubit to dimension m. "
                            + "Put d = ψ(d₀) and e = ψ(e₀). The matrix d₀ is diagonal, so the defining identity "
                            + "of IsMIO makes d diagonal. Positivity of ψ gives d ≥ 0 and d ± e ≥ 0; "
                            + "trace preservation gives tr(d) = 1 and tr(e) = 0. These are exactly the "
                            + "conditions in the preceding norm calculation.")),
                    Paragraph(Text(
                        "For 0 ≤ t ≤ 1, the matrix ρₜ = d₀ + t e₀ has diagonal entries 1/2 and "
                            + "off-diagonal entries t/2. It is the convex combination of d₀ + e₀ and d₀ − e₀ "
                            + "with weights (1 + t)/2 and (1 − t)/2, and its trace is one. Consequently "
                            + "Θₜ(A) = tr(A)ρₜ is a channel. If t ≠ 0 it is not maximally incoherent: "
                            + "applying it to the diagonal matrix |0⟩⟨0| gives ρₜ, whose (0,1) entry t/2 is nonzero.")),
                    Paragraph(Text(
                        "To compute the induced norm on all complex matrices, first prove "
                            + "|tr(A)| ≤ traceNorm(A). A zero trace gives the inequality by nonnegativity. "
                            + "Otherwise set c = conjugate(tr(A))/|tr(A)|. The diagonal matrix cI is unitary "
                            + "and Re tr(cA) = |tr(A)|. The variational formula expressing traceNorm(A) "
                            + "as the maximum real trace over left multiplication by unitaries gives the inequality. "
                            + "It follows that, for any output matrix h and input dimension a ≥ 1, "
                            + "the map A ↦ tr(A)h has induced trace norm traceNorm(h): scalar homogeneity "
                            + "and the trace inequality give the upper bound on the unit ball, while the "
                            + "diagonal projector onto coordinate zero has trace and trace norm one and attains it.")),
                    Paragraph(Text(
                        "For 0 ≤ l ≤ 1 set δ = |2l − 1| and t = δ/2. For each maximally incoherent ψ, "
                            + "use d = ψ(d₀), e = ψ(e₀) and f = l e − (1 − l)UeU† as above. "
                            + "The phase channel fixes ψ(I₂), since it fixes ψ(I₂/2) and the nonzero scalar "
                            + "1/2 can be cancelled. Dephasing preserves the input trace. Expanding ρₜ "
                            + "and the compositions therefore identifies the map in the optimization with "
                            + "A ↦ tr(A)H, where H = (2l − 1)d + t f. Since 0 ≤ t ≤ δ, its induced "
                            + "trace norm is traceNorm(H) = δ for every such ψ.")),
                    Paragraph(Text(
                        "When m ≥ 1, sending A to tr(A)|0⟩⟨0| in dimension m gives a maximally incoherent "
                            + "post-processing: it is a channel and both sides of its dephasing identity equal "
                            + "the same scalar multiple of the diagonal projector. The set of norm values "
                            + "in the optimization is therefore the singleton {δ}. Its real supremum is δ, "
                            + "and l − (1 − l) = 2l − 1, so postImprovement(l,φ,Θₜ) = δ − δ = 0.")),
                    Paragraph(Text(
                        "Finally, l ≠ 1/2 implies δ ≠ 0 and t ≠ 0, while 0 ≤ l ≤ 1 gives δ ≤ 1 "
                            + "and hence 0 ≤ t ≤ 1. Thus Θₜ is a qubit channel that is not maximally incoherent "
                            + "and has zero optimized improvement. This proves failure of faithfulness "
                            + "for every biased prior, every positive phase dimension and every phase function, "
                            + "answering the faithfulness part of the question in Section IV (TeX line 300). "
                            + "The construction includes the endpoint priors and requires no separation between the phases."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("mtp-postprocessed-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula DephaseFormula() => All("n", Naturals(),
        Equal(Typed(Local("dephase"), Maps(X("n"), X("n"))),
            Compose(At(Qualified("Matrix", "diagonalLinearMap"), FinOf(X("n")), Complexes(), Complexes()),
                At(Qualified("Matrix", "diagLinearMap"), FinOf(X("n")), Complexes(), Complexes()))));

    private static Formula MioFormula() => All("a", Naturals(), All("b", Naturals(),
        All("ψ", Maps(X("a"), X("b")), Equivalence(LocalCall("IsMIO", X("ψ")),
            Conjunction(At(Qualified("IsChannel"), X("ψ")), All("x", Matrices(X("a")),
                Equal(At(X("ψ"), LocalCall("dephase", X("x"))),
                    LocalCall("dephase", At(X("ψ"), LocalCall("dephase", X("x")))))))))));

    private static Formula PhaseFormula() => All("m", Naturals(),
        All("φ", Arrow(FinOf(X("m")), Reals()),
            Equal(Typed(LocalCall("phaseChannel", X("φ")), Maps(X("m"), X("m"))),
                At(Qualified("MatrixMap", "conj"), At(Qualified("Matrix", "diagonal"),
                    LambdaOf("i", FinOf(X("m")), At(Qualified("Complex", "exp"),
                        Multiply(At(Qualified("Complex", "ofReal"), At(X("φ"), X("i"))),
                            Qualified("Complex", "I")))))))));

    private static Formula NormFormula() => All("a", Naturals(), All("b", Naturals(),
        All("f", Maps(X("a"), X("b")),
            Equal(Typed(LocalCall("inducedTraceNorm", X("f")), Reals()),
                At(Qualified("sSup"), SetOf("r", Reals(), Some("x", Matrices(X("a")),
                    Conjunction(LE(TraceNorm(X("x")), Typed(D(1), Reals())),
                        Equal(TraceNorm(At(X("f"), X("x"))), X("r"))))))))));

    private static Formula ImprovementFormula()
    {
        Formula weighted = Subtract(
            Smul(At(Qualified("Complex", "ofReal"), X("l")),
                Typed(Qualified("LinearMap", "id"), Maps(X("m"), X("m")))),
            Smul(At(Qualified("Complex", "ofReal"),
                    Subtract(Typed(D(1), Reals()), X("l"))), LocalCall("phaseChannel", X("φ"))));
        Formula composed = Compose(Compose(weighted, X("ψ")), Compose(X("θ"), Local("dephase")));
        Formula values = SetOf("r", Reals(), Some("ψ", Maps(X("b"), X("m")),
            Conjunction(LocalCall("IsMIO", X("ψ")),
                Equal(LocalCall("inducedTraceNorm", composed), X("r")))));
        return All("a", Naturals(), All("b", Naturals(), All("m", Naturals(), All("l", Reals(),
            All("φ", Arrow(FinOf(X("m")), Reals()), All("θ", Maps(X("a"), X("b")),
                Equal(Typed(LocalCall("postImprovement", X("l"), X("φ"), X("θ")), Reals()),
                    Subtract(At(Qualified("sSup"), values),
                        new Formula.Absolute(Subtract(X("l"), Subtract(Typed(D(1), Reals()), X("l"))))))))))));
    }

    private static Formula ResultFormula() => All("l", Reals(),
        Arrow(LE(Typed(D(0), Reals()), X("l")), Arrow(LE(X("l"), Typed(D(1), Reals())),
            Arrow(NotEqual(X("l"), new Formula.Fraction(Typed(D(1), Reals()), Typed(D(2), Reals()))),
                All("m", Naturals(), Arrow(LE(Typed(D(1), Naturals()), X("m")),
                    All("φ", Arrow(FinOf(X("m")), Reals()), Some("θ", Maps(D(2), D(2)),
                        Conjunction(At(Qualified("IsChannel"), X("θ")),
                            Conjunction(new Formula.Not(Parenthesized(LocalCall("IsMIO", X("θ")))),
                                Equal(LocalCall("postImprovement", X("l"), X("φ"), X("θ")),
                                    Typed(D(0), Reals()))))))))))));

    private static Formula X(string name) => name switch
    {
        "φ" => Phi,
        "ψ" => Psi,
        "θ" => Theta,
        _ => F.Id(name),
    };
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
    private static Formula Local(string name) => Qualified(name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula dimension) => At(Qualified("Fin"), dimension);
    private static Formula Matrices(Formula dimension) => At(Qualified("Matrix"), FinOf(dimension), FinOf(dimension), Complexes());
    private static Formula Maps(Formula input, Formula output) => At(Qualified("MatrixMap"), FinOf(input), FinOf(output), Complexes());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, X(name), Colon, Sp, type, Sp, Mid, Sp, Parenthesized(body), CloseBrace);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Smul(Formula scalar, Formula vector) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Compose(Formula first, Formula second) => At(Qualified("LinearMap", "comp"), first, second);
    private static Formula TraceNorm(Formula value) => At(Qualified("traceNorm"), value);
}
