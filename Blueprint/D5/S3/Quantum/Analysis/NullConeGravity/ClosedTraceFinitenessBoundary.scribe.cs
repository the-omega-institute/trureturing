using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class ClosedTraceFinitenessBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary.";

    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    private static DocumentBlock.Describe Def(string name, string id, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(NullCone),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive trace-class dimension bounds, cycle-union variance bounds, and exact rearrangement boundaries for closed traces.",
        H("Closed-trace finiteness boundaries"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closed-trace-finrank-le-of-lower-bound"),
                DeclarationHandle.Create(Prefix + "finiteDimensional_and_finrank_le_of_isTraceClass_lower_bound"),
                H("Finite dimensionality and dimension bound from a trace-class lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("If W ≥ 0 is trace-class on a complex Hilbert space H and satisfies c ‖x‖² ≤ Re ⟪x, W x⟫ "
                    + "for all x with c > 0, then H is finite-dimensional and finrank ℂ H ≤ (trace W).re / c."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closed-trace-finrank-range-le-of-lower-bound"),
                DeclarationHandle.Create(Prefix + "finiteDimensional_and_finrank_range_le_of_isTraceClass_lower_bound"),
                H("Spectral-sublevel dimension bound from a trace-class cylinder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("If C ≥ 0 is trace-class on H and satisfies c ‖x‖² ≤ Re ⟪x, C x⟫ on the range of a star projection p "
                    + "(c > 0), then range p is finite-dimensional with finrank ℂ (range p) ≤ (trace C).re / c, "
                    + "matching the positive content of Chandrasekaran (arXiv:2611.34924v1, Appendix E, Eq. E.12)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closed-trace-cycle-variance-bound"),
                DeclarationHandle.Create(Prefix + "cycle_union_area_variance_bound"),
                H("Positive cycle-union area-variance bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Proves the weighted variance bound Δs² + sMax² / (r c) on any finite union of cycles "
                    + "with at most a 1/r fraction of states outside a band of half-width Δs and weights in [c, 1] "
                    + "(Chandrasekaran, arXiv:2611.34924v1, Appendix D.2, Eq. D.25)."))),
                DescribeRole.Theorem),
            Def("toyArea", "closed-trace-toy-area", "Bounded two-level area function on ℕ",
                "Assigns area 0 to even indices and 1 to odd indices on the orthonormal basis ℕ of ℓ²(ℕ)."),
            Def("pairFlipBoostKernel", "closed-trace-pair-flip-kernel", "Two-sided pair-flip boost difference kernel",
                "Off-diagonal kernel of Δ_η(-σ_x ⊗ σ_x) at boost phase (-1)^{toyArea}, equal to 2 on matched pairs {2m, 2m+1}."),
            Def("subtractedKernel", "closed-trace-subtracted-kernel", "Subtracted boost observable kernel",
                "Kernel of X = Δ_η O − (δ_η/2) I with δ_η = 2."),
            Def("cutAmplitudeX", "closed-trace-cut-amplitude", "Finite-rank closed-cut amplitude",
                "Unnormalized closed-cut expectation Z_F[X] = ∑_{i,j ∈ F} subtractedKernel i j on a finite basis subset F."),
            Def("symCut", "closed-trace-sym-cut", "Symmetric pair cutoff",
                "First N matched pairs {0, ..., 2N − 1}."),
            Def("cycleElement", "closed-trace-cycle-element", "Order-r cycle element",
                "Places one odd index 2n + 1 with r − 1 even indices in the n-th r-cycle."),
            Def("cycleBlockEquiv", "closed-trace-cycle-block-equiv", "Cycle decomposition bijection",
                "Explicit bijection ℕ × Fin r ≃ ℕ partitioning ℕ into disjoint r-cycles."),
            Def("cycleShiftPerm", "closed-trace-cycle-shift-perm", "Order-r cycle permutation",
                "Permutation V_r on ℕ of exact order r whose orbits are the r-cycles of cycleBlockEquiv."),
            Def("cycCut", "closed-trace-cyc-cut", "Finite union of complete r-cycles",
                "Union of the first N complete r-cycles of cycleShiftPerm."),
            Describe.Lean(
                DescribeId.Create("closed-trace-cycle-rearrangement-sign-flip"),
                DeclarationHandle.Create(Prefix + "cycle_rearrangement_sign_flip"),
                H("Closed-trace rearrangement sign-flip counterexample"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(
                    Paragraph(Text("Isolates the exact analytical gap in Chandrasekaran (arXiv:2611.34924v1, Section 5.2, Eq. 5.38). "
                        + "On the infinite basis ℕ with C_b = 1 and bounded area in [0, 1], both symCut N and cycCut r N (r ≥ 5) "
                        + "exhaust ℕ (so their projections converge strongly to 1), and cycCut r N is invariant under the order-r "
                        + "cycle permutation V_r. Yet cutAmplitudeX (symCut N) = 2N → +∞ while cutAmplitudeX (cycCut r N) = (4 − r)N ≤ −N → −∞.")),
                    Paragraph(Text("Hence strong convergence of cycle-union projections plus Z_P[X] ≤ 0 < Z_sym[X] does not contradict "
                        + "infinite dimensionality without an independent trace-class or rearrangement-invariance hypothesis on closed traces."))),
                DescribeRole.Theorem),
            Def("jointCutTerm", "closed-trace-joint-cut-term", "Disjoint joint-cut summand",
                "Product summand f(i, a) = w_i v_a (1_I(a) − p) on ℕ × α."),
            Describe.Lean(
                DescribeId.Create("closed-trace-disjoint-joint-cut-summable-iff"),
                DeclarationHandle.Create(Prefix + "disjoint_joint_cut_summable_iff"),
                H("Exact summability equivalence for disjoint joint cuts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Settles the exact logical content of Chandrasekaran (arXiv:2611.34924v1, Eqs. 5.44–5.45): "
                    + "for any nonnegative sequence w and non-degenerate finite distribution v with p = ∑_{a ∈ I} v_a ∈ (0, 1), "
                    + "every fiber sum vanishes identically (∑_a f(i, a) = 0 even when w is non-summable), the fiber L¹ norm equals "
                    + "2 p (1 − p) w_i, and unconditional summability of f over ℕ × α holds if and only if Summable w already holds."))),
                DescribeRole.Theorem))));
}
