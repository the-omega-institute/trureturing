using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class LongCoreOmissionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact all-length long-core omission scores", H("Exact all-length long-core omission scores"),
        Blocks(Paragraph(Text("Actual induced path constraints extract the original Cell and Across premises from every dissociation selection. Pair-full indicators implement the score-preserving normalization. A score-thirteen open cell contains both matched boundary H pairs; the actual H seam excludes neighboring exceptional cells, including a singleton. Symbolic permutation summation gives the upper bound and the separated A/B word has exactly floor(k/2) A cells, attaining score twelve k plus floor(k/2) for every length. This is the open-H long core, distinct from ClosedCore.")),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 20).", DescribeRole.Definition),
            Node("bit", "bit", "Exact declaration: def bit (S : Finset (Fin 20)) (f : Bool) (v : Fin 20) : ℕ.", DescribeRole.Definition),
            Node("full", "full", "Exact declaration: def full (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) : ℕ.", DescribeRole.Definition),
            Node("cell", "cell", "Exact declaration: def cell (S : Finset (Fin 20)) (f : Bool) : Fin 3 → Cell.", DescribeRole.Definition),
            Node("omitted", "omitted", "Exact declaration: def omitted (S : Finset (Fin 20)) (f : Bool) : ℕ.", DescribeRole.Definition),
            Node("local_bound", "local bound", "Exact declaration: theorem local_bound (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) : S.card+omitted S false≤13 ∧ (S.card+omitted S false=13 → 0∈S ∧ 1∈S ∧ 4∈S ∧ 5∈S).", DescribeRole.Theorem),
            Node("slice", "slice", "Exact declaration: def slice (S : Finset (I × Fin 20)) (i : I) : Finset (Fin 20).", DescribeRole.Definition),
            Node("omissions", "omissions", "Exact declaration: def omissions (S : Finset (I × Fin 20)) : ℕ.", DescribeRole.Definition),
            Node("exceptional_exclusion", "exceptional exclusion", "Exact declaration: theorem exceptional_exclusion (e : Equiv.Perm I) (S : Finset (I × Fin 20)) (hS : IsKIndependent (LongCoreWord.graph e) 2 S) (i : I) : ¬ ( (slice S i).card+omitted (slice S i) false=13 ∧ (slice S (e i)).card+omitted (slice S (e i)) false=13).", DescribeRole.Theorem),
            Node("score_bound", "score bound", "Exact declaration: theorem score_bound (e : Equiv.Perm I) (S : Finset (I × Fin 20)) (hS : IsKIndependent (LongCoreWord.graph e) 2 S) : S.card+omissions S≤12*Fintype.card I+Fintype.card I/2.", DescribeRole.Theorem),
            Node("cyclicWord", "cyclicWord", "Exact declaration: def cyclicWord {k : ℕ} (i : Fin k) : Bool.", DescribeRole.Definition),
            Node("cyclicWord_separated", "cyclicWord separated", "Exact declaration: theorem cyclicWord_separated (k : ℕ) : ∀ i : Fin k, ¬ (cyclicWord i=true ∧ cyclicWord (finRotate k i)=true).", DescribeRole.Theorem),
            Node("cyclicWord_count", "cyclicWord count", "Exact declaration: theorem cyclicWord_count (k : ℕ) : (Finset.univ.filter (fun i : Fin k => cyclicWord i=true)).card=k/2.", DescribeRole.Theorem),
            Node("cyclic_score", "cyclic score", "Exact declaration: theorem cyclic_score (k : ℕ) : (∀ S : Finset (Fin k × Fin 20), IsKIndependent (LongCoreWord.graph (finRotate k)) 2 S → S.card+omissions S≤12*k+k/2) ∧ ∃ S : Finset (Fin k × Fin 20), IsKIndependent (LongCoreWord.graph (finRotate k)) 2 S ∧ S.card+omissions S=12*k+k/2.", DescribeRole.Theorem)), []));
}
