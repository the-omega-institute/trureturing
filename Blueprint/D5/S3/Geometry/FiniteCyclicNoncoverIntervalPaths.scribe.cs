using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

// Source mirrors only. Native projection, ownership and coverage are OPEN.
internal sealed class FiniteCyclicNoncoverIntervalPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cyclic noncover source construction.", H("FiniteCyclicNoncoverIntervalPaths"),
        Blocks(
            Paragraph(Text("Universal proof bodies are attempted source. No compiler, kernel, Scribe/Reg audit or admission was executed. Every handle names its exact D5 source owner. Section variables below are lexical context only, not an asserted compiled telescope. FromLean requests the native projection; no fixture or readout is fabricated.")),
            Node("decl-1", "intervalEmbedding", "intervalEmbedding", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef intervalEmbedding {n : Nat} (lo m : Nat) (h : lo+m ≤ n) : Fin m ↪ Fin n", DescribeRole.Definition),
            Node("decl-2", "intervalList", "intervalList", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef intervalList {n : Nat} (hn : 0 < n) (lo m : Nat) : List (Fin n)", DescribeRole.Definition),
            Node("decl-3", "intervalList_source", "intervalList_source", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem intervalList_source {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n) :\n    intervalList hn lo m = ((List.finRange n).drop lo).take m ∧\n    intervalList hn lo m = (List.finRange m).map (intervalEmbedding lo m h)", DescribeRole.Theorem),
            Node("decl-4", "mem_paths_interval", "mem_paths_interval", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem mem_paths_interval {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n)\n    (a : Finset (Fin n)) :\n    a ∈ paths (intervalList hn lo m) ↔\n      (∀ i ∈ a, lo ≤ i.val ∧ i.val < lo+m) ∧\n      (∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m → i ∉ a ∨ successor hn i ∉ a)", DescribeRole.Theorem),
            Node("decl-5", "mem_pathChosen_interval", "mem_pathChosen_interval", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem mem_pathChosen_interval {n : Nat} (hn : 0 < n) (lo m : Nat)\n    (h : lo+m ≤ n) (i : Fin n) :\n    i ∈ pathChosen (intervalList hn lo m) ↔\n      lo+1 ≤ i.val ∧ i.val < lo+m ∧ (i.val-lo) % 3 = 1", DescribeRole.Theorem),
            Node("decl-6", "pinnedImage", "pinnedImage", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef pinnedImage {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) (lo m : Nat)\n    (S : Finset (Fin n)) : Finset (Finset V)", DescribeRole.Definition),
            Node("decl-7", "pinnedImage_iff", "pinnedImage_iff", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem pinnedImage_iff {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) (lo m : Nat)\n    (h : lo+m ≤ n) (S : Finset (Fin n))\n    (hS : ∀ i ∈ S, i.val < lo ∨ lo+m ≤ i.val) (a : Finset V) :\n    a ∈ pinnedImage hn s lo m S ↔ a ⊆ ground s ∧\n      (∀ i : Fin n, (i.val < lo ∨ lo+m ≤ i.val) → (s i ∉ a ↔ i ∈ S)) ∧\n      (∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m →\n        s i ∈ a ∨ s (successor hn i) ∈ a)", DescribeRole.Theorem),
            Node("decl-8", "survivors_pinnedImage", "survivors_pinnedImage", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem survivors_pinnedImage {n : Nat} (hn : 0 < n) (s : Fin n ↪ V)\n    (k lo m : Nat) (hk : k ≤ lo) (h : lo+m ≤ n) (S : Finset (Fin n))\n    (hS : ∀ i ∈ S, i.val < lo ∨ lo+m ≤ i.val) :\n    survivors (pinnedImage hn s lo m S) (((List.finRange n).drop k).map s) =\n      if m % 3 = 1 then ∅ else\n        {complementMap s (S ∪ pathChosen (intervalList hn lo m))}", DescribeRole.Theorem))));
    private static DocumentBlock Node(string id, string declaration, string title,
        string prose, string rawContract, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose)), Paragraph(Text(rawContract))), role);
}
