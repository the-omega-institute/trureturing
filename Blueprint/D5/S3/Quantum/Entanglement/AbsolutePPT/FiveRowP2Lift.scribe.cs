using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;
internal sealed class FiveRowP2LiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral gaps reconstruct an arbitrary ordered nonnegative vector. Concentrating its middle gaps preserves the boundary values; convexity transfers a quadratic upper bound from the concentrated vectors.", H("FiveRowP2Lift"), Blocks(
            Paragraph(Text("Spectral gaps reconstruct an arbitrary ordered nonnegative vector. Concentrating its middle gaps preserves the boundary values; convexity transfers a quadratic upper bound from the concentrated vectors.")),
            Describe.Lean(DescribeId.Create("fiverowp2lift-middle"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middle"),
                H("middle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def middle (N : ℕ) : Finset (Fin N)"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fiverowp2lift-middlemass"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middleMass"),
                H("middleMass"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fiverowp2lift-frozen"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.frozen"),
                H("frozen"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def frozen {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fiverowp2lift-concentrated"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated"),
                H("concentrated"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def concentrated {N : ℕ} (g : Fin N → ℝ) (j : Fin N) : Fin N → ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fiverowp2lift-concentrated-nonnegative"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated_nonnegative"),
                H("concentrated nonnegative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem concentrated_nonnegative {N : ℕ} (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i,0 ≤ l i) (j : Fin N) : ∀ k,0 ≤ concentrated (spectralGap l) j k"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fiverowp2lift-middle-mass-actual"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middle_mass_actual"),
                H("middle mass actual"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem middle_mass_actual {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : middleMass (spectralGap l) = l ⟨9,by omega⟩-l ⟨N-15,by omega⟩"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fiverowp2lift-concentrated-boundary"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated_boundary"),
                H("concentrated boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem concentrated_boundary {N : ℕ} (l : Fin N → ℝ) (j : Fin N) (hj : j ∈ middle N) (k : Fin N) (hk : k.val < 10 ∨ N-15 ≤ k.val) : concentrated (spectralGap l) j k = l k"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fiverowp2lift-gap-convex-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.gap_convex_identity"),
                H("gap convex identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem gap_convex_identity {N : ℕ} (l : Fin N → ℝ) (hv : 0 < middleMass (spectralGap l)) : (∑ j ∈ middle N, (spectralGap l j/middleMass (spectralGap l)) • concentrated (spectralGap l) j) = l"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fiverowp2lift-zero-middle"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.zero_middle"),
                H("zero middle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem zero_middle {N : ℕ} (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i) (hv : middleMass (spectralGap l)=0) (j : Fin N) : concentrated (spectralGap l) j = l"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fiverowp2lift-concentration-transfer"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentration_transfer"),
                H("concentration transfer"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem concentration_transfer {N : ℕ} (hN : 25 ≤ N) (theta : ℝ) (ht : 0 ≤ theta) (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i) (hc : ∀ j ∈ middle N, 0 ≤ ∑ i, concentrated (spectralGap l) j i) (hb : ∀ j ∈ middle N, ∑ i, (concentrated (spectralGap l) j i)^2 ≤ theta*(∑ i, concentrated (spectralGap l) j i)^2) : ∑ i, (l i)^2 ≤ theta*(∑ i, l i)^2"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fiverowp2lift-augmented-norm-lift"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.augmented_norm_lift"),
                H("augmented norm lift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem augmented_norm_lift {I J : Type*} [Fintype I] [Fintype J] (p : I → ℝ) (x : I → J → ℝ) (l : J → ℝ) (theta c : ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) (ht : 0 ≤ theta) (hc : 0 ≤ c) (hm : ∀ i, 0 ≤ ∑ j, x i j) (hr : ∀ j, l j=∑ i, p i*x i j) (hb : ∀ i, (∑ j, (x i j)^2)+c ≤ theta*(∑ j, x i j)^2) : (∑ j, (l j)^2)+c ≤ theta*(∑ j, l j)^2"))), DescribeRole.Theorem)
        )));
}
