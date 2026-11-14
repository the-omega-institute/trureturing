using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EffectAdditivityStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary defect on all actual effects controls real scaling and signed finite families.",
        H("Effect additivity stability"),
        Blocks(
            Paragraph(Text("Write Mat d for Matrix (Fin d) (Fin d) Complex, with d any natural number. An effect E means that E is positive semidefinite and identity minus E is positive semidefinite. Every displayed p is an arbitrary total real function on these actual matrices; only its effect values enter the estimates.")),
            Paragraph(Text("The interval argument applies a supremum contraction to g(t)=p(t*E)-t*p(E). Positivity and normalization bound this function; binary defect gives the contraction. A nonempty weighted list then accumulates its binary and homogeneity errors. Splitting signed coefficients and rescaling by K squared gives the general finite-family estimate. Zero terms are retained throughout.")),
            Describe.Lean(
                DescribeId.Create("mat"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.Mat"),
                H("Mat"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The matrix space in dimension d is the actual complex square matrix algebra indexed by Fin d.")),
                    Paragraph(Text("abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.IsEffect"),
                H("IsEffect"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An effect is an actual positive semidefinite complex matrix whose complement to the identity is also positive semidefinite.")),
                    Paragraph(Text("def IsEffect {d : ℕ} (E : Mat d) : Prop := E.PosSemidef ∧ (1 - E).PosSemidef"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("effect-iff-order"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.effect_iff_order"),
                H("effect iff order"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two positive semidefinite conditions defining an effect are equivalent to the native matrix-order interval from zero to the identity.")),
                    Paragraph(Text("theorem effect_iff_order {d : ℕ} (E : Mat d) : IsEffect E ↔ 0 ≤ E ∧ E ≤ 1"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cstar-effect-bridge"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.cstar_effect_bridge"),
                H("cstar effect bridge"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The native C-star matrix equivalence identifies the same actual effects with its order interval from zero to one.")),
                    Paragraph(Text("theorem cstar_effect_bridge {d : ℕ} (X : CStarMatrix (Fin d) (Fin d) ℂ) : IsEffect (CStarMatrix.ofMatrix.symm X) ↔ 0 ≤ X ∧ X ≤ 1"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-interval-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.bounded_interval_stability"),
                H("bounded interval stability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every bounded real function g on the unit interval with g(1)=0 and binary additive defect at most epsilon has absolute value at most twice epsilon throughout that interval. The bound M is arbitrary; no continuity or measurability is assumed.")),
                    Paragraph(Text("theorem bounded_interval_stability (g : ℝ → ℝ) (ε M : ℝ) (hε : 0 ≤ ε) (h1 : g 1 = 0) (hb : ∀ t, 0 ≤ t → t ≤ 1 → |g t| ≤ M) (ha : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ 1 → |g (s + t) - g s - g t| ≤ ε) : ∀ t, 0 ≤ t → t ≤ 1 → |g t| ≤ 2 * ε"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probability-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.probability_bounds"),
                H("probability bounds"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Nonnegativity on all effects, normalization at the identity and the stated binary defect imply that p(0) lies between zero and epsilon, and every effect value lies between zero and 1+epsilon. No separate sign premise on epsilon is added.")),
                    Paragraph(Text("theorem probability_bounds {d : ℕ} (p : Mat d → ℝ) (ε : ℝ) (hpos : ∀ E, IsEffect E → 0 ≤ p E) (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) → |p (E+F) - p E - p F| ≤ ε) (hnorm : p 1 = 1) : (0 ≤ p 0 ∧ p 0 ≤ ε) ∧ ∀ E, IsEffect E → 0 ≤ p E ∧ p E ≤ 1+ε"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("effect-homogeneity"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.effect_homogeneity"),
                H("effect homogeneity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every actual effect and every real scale in the closed unit interval, the homogeneity error is at most 2*epsilon, under precisely the displayed global positivity, normalization and binary-defect hypotheses.")),
                    Paragraph(Text("theorem effect_homogeneity {d : ℕ} (p : Mat d → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hpos : ∀ E, IsEffect E → 0 ≤ p E) (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) → |p (E+F) - p E - p F| ≤ ε) (hnorm : p 1 = 1) (E : Mat d) (hE : IsEffect E) : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |p (t • E) - t*p E| ≤ 2*ε"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-sum-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.finite_sum_error"),
                H("finite sum error"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A list of n+1 positive semidefinite matrices whose total is an effect accumulates at most n*epsilon additive error. Only binary-defect control is assumed; no p(0)=0 or additional epsilon-sign premise is imposed.")),
                    Paragraph(Text("theorem finite_sum_error {d : ℕ} (p : Mat d → ℝ) (ε : ℝ) (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) → |p (E+F) - p E - p F| ≤ ε) : ∀ n : ℕ, ∀ A : Fin (n+1) → Mat d, (∀ i, (A i).PosSemidef) → IsEffect (∑ i, A i) → |p (∑ i, A i) - ∑ i, p (A i)| ≤ (n : ℝ)*ε"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-finite-sum-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.weighted_finite_sum_error"),
                H("weighted finite sum error"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For n+1 effects with real weights in the closed unit interval and an effect-valued weighted total, the weighted error is at most (3*(n+1)-1)*epsilon, with n interpreted in the reals.")),
                    Paragraph(Text("theorem weighted_finite_sum_error {d n : ℕ} (p : Mat d → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hpos : ∀ E, IsEffect E → 0 ≤ p E) (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) → |p (E+F)-p E-p F| ≤ ε) (hnorm : p 1 = 1) (B : Fin (n+1) → Mat d) (t : Fin (n+1) → ℝ) (hB : ∀ i, IsEffect (B i)) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (hS : IsEffect (∑ i, t i • B i)) : |p (∑ i, t i • B i) - ∑ i, t i * p (B i)| ≤ (3 * ((n : ℝ)+1)-1) * ε"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-fintype-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.weighted_fintype_error"),
                H("weighted fintype error"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The same weighted estimate holds for every nonempty finite index type, including zero coefficients, with constant 3*card(I)-1 and all displayed effect, weight and total conditions preserved.")),
                    Paragraph(Text("theorem weighted_fintype_error {d : ℕ} {I : Type*} [Fintype I] [Nonempty I] (p : Mat d → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hpos : ∀ E, IsEffect E → 0 ≤ p E) (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) → |p (E+F)-p E-p F| ≤ ε) (hnorm : p 1 = 1) (B : I → Mat d) (t : I → ℝ) (hB : ∀ i, IsEffect (B i)) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (hS : IsEffect (∑ i, t i • B i)) : |p (∑ i, t i • B i) - ∑ i, t i * p (B i)| ≤ (3 * (Fintype.card I : ℝ)-1) * ε"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-positive-family-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectAdditivityStability.finite_positive_family_error"),
                H("finite positive family error"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural matrix dimension and nonempty finite index type I, any effect family with sum at most K times the identity and signed real coefficients of absolute value at most K represents each specified effect E with probability error at most K^2*(6*card(I)+1)*epsilon. The premises require K>=1 and epsilon>=0 and the actual equality for E; the dimension need not be positive in this general helper.")),
                    Paragraph(Text("theorem finite_positive_family_error {d : ℕ} {I : Type*} [Fintype I] [Nonempty I] (p : Mat d → ℝ) (ε K : ℝ) (hε : 0 ≤ ε) (hK : 1 ≤ K) (hpos : ∀ E, IsEffect E → 0 ≤ p E) (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) → |p (E+F)-p E-p F| ≤ ε) (hnorm : p 1 = 1) (B : I → Mat d) (c : I → ℝ) (hB : ∀ i, IsEffect (B i)) (hBsum : (∑ i, B i) ≤ K • (1 : Mat d)) (hc : ∀ i, |c i| ≤ K) (E : Mat d) (hE : IsEffect E) (hrepr : E = ∑ i, c i • B i) : |p E - ∑ i, c i * p (B i)| ≤ K^2 * (6 * (Fintype.card I : ℝ)+1) * ε"))),
                DescribeRole.Theorem))));
}
