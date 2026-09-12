using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeReal;

internal sealed class BisectionCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational midpoint bisection identifies its lower Cauchy class as a least upper bound.",
        H("Bisection Completion"),
        Blocks(
            Paragraph(Text(
                "All sequences and subsets here are native Lean mathematical objects. "
                + "QSeq is the full rational Cauchy sequence type and QHat its zero-difference quotient. "
                + "For S : Set QHat and l u : ℚ, write hl for lower non-upperness and hu for upperness. "
                + "The consequences O1–O11 below preserve complete statements by direct derivation; "
                + "they have no separate declaration anchors or independent coverage claim. "
                + "This component does not establish the rich-real interpretation, internal ZFC coding, "
                + "definition elimination or conservativity.")),
            Describe.Lean(
                DescribeId.Create("qseq"), DeclarationHandle.Create(Prefix + "QSeq"),
                H("Rational Cauchy sequences"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The sequence type consists of all rational sequences satisfying the rational "
                        + "absolute-value Cauchy condition."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qhat"), DeclarationHandle.Create(Prefix + "QHat"),
                H("The rational Cauchy quotient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the standard quotient of rational Cauchy sequences by zero-limit "
                        + "difference, with its existing field operations.")),
                    Paragraph(Text(
                        "O4 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: (q : ℚ) : CauSeq.Completion.mk (CauSeq.const abs q) = (q : QHat).")),
                    Paragraph(Text(
                        "Derivation: Use toReal.injective, O3 on the constant sequence, supplied Real.mk_const, "
                        + "and map_ratCast, exactly the original proof's normalization.")),
                    Paragraph(Text(
                        "O5 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: : Function.Injective (fun q : ℚ => CauSeq.Completion.mk (CauSeq.const "
                        + "abs q)).")),
                    Paragraph(Text(
                        "Derivation: Substitute the equality of O4 for each q, then apply Rat.cast_injective into "
                        + "the existing characteristic-zero quotient field. This is the original proof with the "
                        + "omitted equation expanded."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("to-real"), DeclarationHandle.Create(Prefix + "toReal"),
                H("The ring equivalence with the reals"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The inverse of Real.ringEquivCauchy identifies this quotient with the real field.")),
                    Paragraph(Text(
                        "O1 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: : QHat ≃o ℝ.")),
                    Paragraph(Text(
                        "Derivation: Use the existing record expression { toReal.toEquiv with map_rel_iff' := "
                        + "Iff.rfl }; completionOrder is exactly the lifted real order.")),
                    Paragraph(Text(
                        "O3 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: (a : QSeq) : toReal (CauSeq.Completion.mk a) = Real.mk a.")),
                    Paragraph(Text(
                        "Derivation: Unfold the surviving toReal and the supplied Real.ringEquivCauchy/Real.mk "
                        + "definitions; the equality is reflexive, as in the original body.")),
                    Paragraph(Text(
                        "O7 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: (x : QHat) : ∃ l u : ℤ, (l : QHat) < x ∧ x < (u : QHat).")),
                    Paragraph(Text(
                        "Derivation: Apply existing exists_int_lt and exists_int_gt to toReal x. Normalize toReal "
                        + "of integer casts by the ring equivalence and the lifted order. Keep both strict "
                        + "inequalities and both integer witnesses, as in the original body."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("completion-order"), DeclarationHandle.Create(Prefix + "completionOrder"),
                H("The induced linear order"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For x y : QHat, x ≤ y means toReal x ≤ toReal y, and likewise for strict order."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("completion-ordered-ring"), DeclarationHandle.Create(Prefix + "completionOrderedRing"),
                H("Order agrees with field operations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The existing quotient field operations satisfy IsStrictOrderedRing under this induced "
                        + "order, by Function.Injective.isStrictOrderedRing."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("completion-metric"), DeclarationHandle.Create(Prefix + "completionMetric"),
                H("The induced metric"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For x y : QHat, dist x y = dist (toReal x) (toReal y) by definition of "
                        + "MetricSpace.induced.")),
                    Paragraph(Text(
                        "O2 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: : Isometry toReal.")),
                    Paragraph(Text(
                        "Derivation: Apply the existing Mathlib Isometry.of_dist_eq to the definitional equality "
                        + "of the induced distance with dist (toReal x) (toReal y), exactly the original one-line "
                        + "body."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-cauchy-iff-real"), DeclarationHandle.Create(Prefix + "rational_cauchy_iff_real"),
                H("Rational and real Cauchy conditions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A rational sequence satisfies the absolute-value Cauchy condition exactly when its real "
                        + "casts form a metric Cauchy sequence."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-terms-tendsto"), DeclarationHandle.Create(Prefix + "rational_terms_tendsto"),
                H("Terms converge to their own class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the real metric, the terms of a rational Cauchy sequence converge to the real image "
                        + "of their own completion class. The estimate comes directly from the Cauchy condition."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-radius"), DeclarationHandle.Create(Prefix + "dyadicRadius"),
                H("Dyadic approximation errors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The error at index n is the reciprocal of the nth power of two.")),
                    Paragraph(Text(
                        "O6 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: (n : ℕ) : 0 < dyadicRadius n.")),
                    Paragraph(Text(
                        "Derivation: Unfold the surviving radius definition; positivity of 2, its nth power and "
                        + "its inverse yields the original assertion. This is the existing positivity "
                        + "normalization, with no additional premise."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-radius-tendsto"), DeclarationHandle.Create(Prefix + "dyadic_radius_tendsto"),
                H("Errors tend to zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The dyadic approximation errors converge to zero."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("midpoint-step"), DeclarationHandle.Create(Prefix + "midpointStep"),
                H("The rational midpoint step"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Test whether the constant class of the rational midpoint is an upper bound of the set. "
                        + "If so, retain the lower half of the interval; otherwise retain the upper half. The test "
                        + "is classical and asserts no executable decision procedure."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bisect"), DeclarationHandle.Create(Prefix + "bisect"),
                H("Iteration from a rational bracket"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Begin with the given pair of rational endpoints and iterate the midpoint step."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lower"), DeclarationHandle.Create(Prefix + "lower"),
                H("Lower endpoints"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The lower endpoint sequence is the first coordinate of each iterated rational interval."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("upper"), DeclarationHandle.Create(Prefix + "upper"),
                H("Upper endpoints"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The upper endpoint sequence is the second coordinate of each iterated rational interval."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nonupper-lt-upper"), DeclarationHandle.Create(Prefix + "nonupper_lt_upper"),
                H("The endpoints are strictly ordered"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A rational whose class is not an upper bound is strictly below any rational whose class "
                        + "is an upper bound."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("midpoint-step-bounds"), DeclarationHandle.Create(Prefix + "midpoint_step_bounds"),
                H("Preservation of bound properties"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A midpoint step preserves the fact that the lower endpoint is not an upper bound and the "
                        + "upper endpoint is an upper bound."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("midpoint-step-halves"), DeclarationHandle.Create(Prefix + "midpoint_step_halves"),
                H("Exact halving"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For either outcome of the midpoint test, the new rational width is exactly half the "
                        + "previous width."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bisection-invariant"), DeclarationHandle.Create(Prefix + "bisection_invariant"),
                H("The midpoint invariant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At every index, the lower class is not an upper bound, the upper class is an upper "
                        + "bound, and the rational width equals the initial width divided by the corresponding "
                        + "power of two. The lower endpoint need not bound all members below."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bisection-nested"), DeclarationHandle.Create(Prefix + "bisection_nested"),
                H("Monotone endpoints"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The lower endpoint sequence is monotone, the upper endpoint sequence is antitone, and "
                        + "the lower endpoint is always strictly below the upper endpoint.")),
                    Paragraph(Text(
                        "O8 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: (S : Set QHat) (l u : ℚ) (hl : (l : QHat) ∉ upperBounds S) (hu : (u : "
                        + "QHat) ∈ upperBounds S) {n m : ℕ} (hnm : n ≤ m) : Icc (lower S l u m) (upper S l u m) ⊆ "
                        + "Icc (lower S l u n) (upper S l u n).")),
                    Paragraph(Text(
                        "Derivation: From the retained bisection_nested take hlo and hup; apply Icc_subset_Icc "
                        + "(hlo hnm) (hup hnm). No new hypothesis or reduced quantification."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bisection-width-tendsto"), DeclarationHandle.Create(Prefix + "bisection_width_tendsto"),
                H("Vanishing widths"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real casts of the rational interval widths converge to zero, by exact halving and "
                        + "the vanishing dyadic radius."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bisection-endpoints-cauchy"), DeclarationHandle.Create(Prefix + "bisection_endpoints_cauchy"),
                H("Both endpoints are Cauchy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Nesting bounds the distance between two later endpoints by an earlier interval width. "
                        + "Consequently both rational endpoint sequences are Cauchy."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-seq"), DeclarationHandle.Create(Prefix + "lowerSeq"),
                H("The lower Cauchy sequence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The lower endpoint sequence, together with its Cauchy proof, defines a rational Cauchy "
                        + "representative.")),
                    Paragraph(Text(
                        "Write L = lowerSeq S l u hl hu and c = CauSeq.Completion.mk L; these proof arguments "
                        + "specify the actual lower endpoint representative."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("upper-seq"), DeclarationHandle.Create(Prefix + "upperSeq"),
                H("The upper Cauchy sequence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The upper endpoint sequence, together with its Cauchy proof, defines a rational Cauchy "
                        + "representative.")),
                    Paragraph(Text(
                        "Write U = upperSeq S l u hl hu. Both endpoint Cauchy proofs and representatives are "
                        + "retained for the completion-class consequence O9."))
                ), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bisection-common-limit-real"), DeclarationHandle.Create(Prefix + "bisection_common_limit_real"),
                H("A common real limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real casts of both endpoint sequences tend to the real image of the lower endpoint "
                        + "class.")),
                    Paragraph(Text(
                        "O9 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: (S : Set QHat) (l u : ℚ) (hl : (l : QHat) ∉ upperBounds S) (hu : (u : "
                        + "QHat) ∈ upperBounds S) : CauSeq.Completion.mk (upperSeq S l u hl hu) = "
                        + "CauSeq.Completion.mk (lowerSeq S l u hl hu) ∧ Tendsto (fun n => (lower S l u n : QHat)) "
                        + "atTop (𝓝 (CauSeq.Completion.mk (lowerSeq S l u hl hu))) ∧ Tendsto (fun n => (upper S l u "
                        + "n : QHat)) atTop (𝓝 (CauSeq.Completion.mk (lowerSeq S l u hl hu))).")),
                    Paragraph(Text(
                        "Derivation: Let hlo,hup be the two projections of the retained "
                        + "bisection_common_limit_real. The retained rational_terms_tendsto U gives convergence of "
                        + "the upper real terms to Real.mk U; tendsto_nhds_unique with hup gives Real.mk U = "
                        + "Real.mk L. Use toReal.injective and O3 to obtain class equality. For each of the two "
                        + "QHat term sequences, apply Isometry.tendsto_nhds_iff with the direct O2 isometry; "
                        + "Function.comp_def, map_ratCast and O3 identify its real image with hlo or hup. Assemble "
                        + "exactly these three assertions. This is the original common_limit body with its omitted "
                        + "trivial wrapper names expanded.")),
                    Paragraph(Text(
                        "Here L = lowerSeq S l u hl hu, U = upperSeq S l u hl hu, and c = CauSeq.Completion.mk L. "
                        + "Class equality and both QHat sequence limits are asserted separately from the real-limit "
                        + "theorem."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bisection-is-lub"), DeclarationHandle.Create(Prefix + "bisection_isLUB"),
                H("The midpoint limit is a least upper bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The upper endpoint limit bounds every member of the set. If an upper bound were below "
                        + "the lower endpoint limit, a sufficiently late lower endpoint would itself be an upper "
                        + "bound, contradicting the invariant.")),
                    Paragraph(Text(
                        "O10 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: (S : Set QHat) (hne : S.Nonempty) (hb : BddAbove S) : ∃ l u : ℚ, (∃ x "
                        + "∈ S, (l : QHat) < x) ∧ (l : QHat) ∉ upperBounds S ∧ (u : QHat) ∈ upperBounds S.")),
                    Paragraph(Text(
                        "Derivation: Choose x∈S from hne and y∈upperBounds S from hb. O7 at x supplies integer "
                        + "a<x; O7 at y supplies integer b>y. Set l=(a:ℚ), u=(b:ℚ). Rat.cast_intCast identifies "
                        + "their QHat casts. The same x witnesses the first conjunct. Upperness of l contradicts "
                        + "l<x; every z∈S satisfies z≤y<u, so u is an upper bound. These are exactly the witnesses "
                        + "and argument of the original bracket proof, with O7 expanded.")),
                    Paragraph(Text(
                        "S may be unbounded below. Only l below one member is required; no lower bound of S is "
                        + "assumed or selected.")),
                    Paragraph(Text(
                        "O11 (direct consequence, without a separate declaration). Exact statement, with the "
                        + "displayed binders: (S : Set QHat) (hne : S.Nonempty) (hb : BddAbove S) : ∃ l u : ℚ, ∃ hl "
                        + ": (l : QHat) ∉ upperBounds S, ∃ hu : (u : QHat) ∈ upperBounds S, (∃ x ∈ S, (l : QHat) < "
                        + "x) ∧ IsLUB S (CauSeq.Completion.mk (lowerSeq S l u hl hu)).")),
                    Paragraph(Text(
                        "Derivation: Take exactly l,u,hx,hl,hu from O10 and form the original existential tuple "
                        + "with the retained bisection_isLUB S l u hl hu. Keep the dependent proof arguments of "
                        + "lowerSeq and the below-member witness. No pre-existing arbitrary supremum replaces this "
                        + "endpoint."))
                ), DescribeRole.Theorem))));
}
