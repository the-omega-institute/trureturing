using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfRawWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/ZeckendorfRawWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual canonical Fibonacci parity windows carry complete partial continuation behavior.",
        H("Decorated Fibonacci Windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-support"),
                DeclarationHandle.Create(Prefix + "support"),
                H("Occupied Fibonacci indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a padded MSD word w over Fin 2, support [] = [] and support (a :: w) = support w if a = 0, otherwise (w.length + 2) :: support w. Indices descend in MSD order; legal words have no adjacent occupied indices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-value"),
                DeclarationHandle.Create(Prefix + "value"),
                H("Padded MSD value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every w : List (Fin 2), value w = (fibPair w).1. Thus the rightmost position has weight F_2 = 1; prepended zeros preserve the value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-parity"),
                DeclarationHandle.Create(Prefix + "parity"),
                H("Canonical Fibonacci parity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n : ℕ, parity n = decide ((wdigits n).length % 2 = 1), the parity of the occupied indices of the canonical Zeckendorf representation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-q"),
                DeclarationHandle.Create(Prefix + "q"),
                H("Decorated numerical source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n : ℕ, q n = (parity n, decide (2 ∈ wdigits n)). The two coordinates record canonical parity and occupation of the least Fibonacci position."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-mu"),
                DeclarationHandle.Create(Prefix + "mu"),
                H("Decorated substitution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a : Bool × Bool, mu a is [(a.1, false)] when a.2 is true, and [(a.1, false), (!a.1, true)] otherwise. Both decorations are retained in the substituted source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-window"),
                DeclarationHandle.Create(Prefix + "window"),
                H("Complete decorated window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For c n : ℕ, window c n = (List.range (c + 1)).map (fun i => q (n + i)). It includes both numerical endpoints n and n + c."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-residual"),
                DeclarationHandle.Create(Prefix + "residual"),
                H("Complete partial continuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For c : ℕ and w z : List (Fin 2), residual c w z is some (parity (value (w ++ z) + c)) when NoAdjacentOnes (w ++ z), and none otherwise. The domain includes every padded legal word and the empty suffix; malformed continuations remain undefined."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-1"),
                DeclarationHandle.Create(Prefix + "source_word_coordinates"),
                H("Padded source coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem source_word_coordinates (w : List (Fin 2)) (hw : NoAdjacentOnes w) : (support w).IsZeckendorfRep ∧ (∀ k ∈ support w, k < w.length + 2) ∧ ((support w).map Nat.fib).sum = (fibPair w).1 ∧ ((support w).map (fun k => Nat.fib (k + 1))).sum = (fibPair w).2`.")),
                    Paragraph(Text("Every legal padded MSD word has canonical occupied indices. The same indices decode the value and its one-position Fibonacci shift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-2"),
                DeclarationHandle.Create(Prefix + "source_expansion"),
                H("Numerical substitution intervals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem source_expansion (n t : ℕ) : ((List.range t).map (fun i => q (n + i))).flatMap mu = (List.range (goldenSubstStart (n + t) - goldenSubstStart n)).map (fun i => q (goldenSubstStart n + i))`.")),
                    Paragraph(Text("Substituting the decorated letters of a numerical interval yields exactly the interval between the corresponding append-zero boundaries. The four images retain parity and the least occupied digit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeckendorfrawwindow-3"),
                DeclarationHandle.Create(Prefix + "window_residual_congruence"),
                H("Complete partial residual congruence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem window_residual_congruence (c : ℕ) (w v : List (Fin 2)) (hw : NoAdjacentOnes w) (hv : NoAdjacentOnes v) (he : window c (value w) = window c (value v)) : residual c w = residual c v`.")),
                    Paragraph(Text("Equality of actual windows implies equality on every suffix, including the empty suffix. The least-digit occupation at the first window position controls extension legality; the parity at the final window position supplies the terminal output. Invalid continuations give none on both sides."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/GoldenBase4IntervalMachine")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Automata/BinaryZeckendorfLanguage")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf"))
        ]));
}
