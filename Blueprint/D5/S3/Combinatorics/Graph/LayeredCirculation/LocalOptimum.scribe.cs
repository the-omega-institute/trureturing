using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LayeredCirculation;

internal sealed class LocalOptimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least five and every real position-dependent five-pattern test, the actual normalized complete-overlap local-law maximum is attained and equals the largest of the one-, two-, and three-turn max-plus trace averages. The transition matrix has exactly the five legal labeled entries; semiring zero means no path. The monodromy is the chronological product of the n heterogeneous matrices. This theorem concerns real local laws and mathematical maxima; it does not assert physical implementation, arbitrary-real computation, or a complexity bound.",
        H("LocalOptimum"),
        Blocks(
            Paragraph(Text("Generic declarations use these source contexts:")),
            Describe.Lean(
                DescribeId.Create("maxplus"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.MaxPlus"),
                H("MaxPlus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: abbrev MaxPlus := Tropical (WithTop (OrderDual ℝ))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("maxscore"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.maxScore"),
                H("maxScore"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def maxScore (x : MaxPlus) : WithBot ℝ := Tropical.untrop x"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("realentry"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.realEntry"),
                H("realEntry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def realEntry (x : ℝ) : MaxPlus := Tropical.trop ((OrderDual.toDual x : OrderDual ℝ) : WithTop (OrderDual ℝ))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("transition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.transition"),
                H("transition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def transition {n : ℕ} (f : ZMod n → Fin 5 → ℝ) (i : ZMod n) : Matrix (Fin 3) (Fin 3) MaxPlus := ![![realEntry (f i 0), realEntry (f i 3), 0], ![0, 0, realEntry (f i 2)], ![realEntry (f i 1), realEntry (f i 4), 0]]"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orderedproduct"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.orderedProduct"),
                H("orderedProduct"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def orderedProduct {n : ℕ} (f : ZMod n → Fin 5 → ℝ) (i : ZMod n) : ℕ → Matrix (Fin 3) (Fin 3) MaxPlus | 0 => 1 | k+1 => orderedProduct f i k * transition f (i+k)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("monodromy"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.monodromy"),
                H("monodromy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def monodromy {n : ℕ} (f : ZMod n → Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) MaxPlus := orderedProduct f 0 n"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("maxtrace"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.maxTrace"),
                H("maxTrace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def maxTrace (M : Matrix (Fin 3) (Fin 3) MaxPlus) : WithBot ℝ := maxScore (Matrix.trace M)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tracevalue"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.traceValue"),
                H("traceValue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def traceValue (M : Matrix (Fin 3) (Fin 3) MaxPlus) : ℝ := (maxTrace M).unbotD 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shortcycleoptimum"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.shortCycleOptimum"),
                H("shortCycleOptimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def shortCycleOptimum {n : ℕ} (f : ZMod n → Fin 5 → ℝ) : ℝ := max (traceValue (monodromy f)) (max (traceValue (monodromy f ^ 2) / 2) (traceValue (monodromy f ^ 3) / 3))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("legalcyclicword"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.LegalCyclicWord"),
                H("LegalCyclicWord"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def LegalCyclicWord {L : ℕ} (u : ZMod L → Bool) : Prop := ∀ j, ¬(u j=true ∧ u (j+1)=true)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("patterncode"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.patternCode"),
                H("patternCode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def patternCode : Bool × Bool × Bool → Fin 5 | (false,false,false) => 0 | (true,false,false) => 1 | (false,true,false) => 2 | (false,false,true) => 3 | (true,false,true) => 4 | _ => 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("window"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.window"),
                H("window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def window {L : ℕ} (u : ZMod L → Bool) (j : ZMod L) : Bool × Bool × Bool := (u j,u (j+1),u (j+2))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("wordscore"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.wordScore"),
                H("wordScore"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def wordScore {n L : ℕ} (f : ZMod n → Fin 5 → ℝ) (u : ZMod L → Bool) : ℝ := ∑ j : Fin L, f (j.val : ZMod n) (patternCode (window u (j.val : ZMod L)))"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("whole-theorem18-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.whole_theorem18_1"),
                H("whole theorem18 1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem whole_theorem18_1 (n : ℕ) (hn : 5 ≤ n) (f : ZMod n → Fin 5 → ℝ) : letI : NeZero n := ⟨by omega⟩ IsGreatest {v : ℝ | ∃ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p ∧ localScore f p=v} (max (traceValue (monodromy f)) (max (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3))) ∧ IsCompact {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p} ∧ {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p}.Nonempty ∧ (∀ p : ZMod n → Fin 5 → ℝ, (IsLocalLaw p ↔ (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ=1) ∧ IsCirculation p)) ∧ (∀ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p → HasPositiveCycleDecomposition p) ∧ (∀ p : ZMod n → Fin 5 → ℝ, (∀ i σ, 0 ≤ p i σ) → IsCirculation p → p ≠ 0 → HasPositiveCycleErasure p) ∧ (∀ m : ℕ, 1 ≤ m → IsGreatest {v : ℝ | ∃ u : ZMod (m*n) → Bool, LegalCyclicWord u ∧ wordScore f u=v} (traceValue (monodromy f ^ m))) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a), w.length=m*n → IsLocalLaw (walkLaw w) ∧ localScore f (walkLaw w)=Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w/m ∧ localScore f (walkLaw w) ≤ shortCycleOptimum f The conjunction includes literal IsGreatest semantics, compactness and nonemptiness, exact local-law/circulation equivalence, positive real cycle decomposition, minimum-edge positive-support erasure, an attained trace identity for every legal periodic word length m*n with m at least one, and the lawful normalized traversal-count construction and average-score bound for every closed walk of that length, including arbitrary repetitions."))),
                DescribeRole.Theorem))));
}
