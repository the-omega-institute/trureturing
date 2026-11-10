using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteCyclicNoncoverGreedyBranchesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches",
            "Actual original s2 no/yes branches and their later-round restrictions, without altering ambient labels.",
            "original-cyclic-second-round",
            Anchor.ParseCanonical("mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic")), H("FiniteCyclicNoncoverGreedyBranches"),
        Blocks(
            Paragraph(Text("The actual original s2 branches, exact free interval predicates, native no/yes restrictions and later-round separation. The interval-to-path-list conjugacy and all-n critical readback remain missing; C02 is absent. Lexical section variables are recorded faithfully. Lean may omit unused variables. ")),
            Node("decl-1", "branchA", "branchA", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchA.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef branchA {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) : Finset (Finset V)", DescribeRole.Definition),
            Node("decl-2", "branchB", "branchB", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchB.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef branchB {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) : Finset (Finset V)", DescribeRole.Definition),
            Node("decl-3", "second_round", "second_round", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.second_round.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem second_round {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :\n    remaining (tailFaces (by omega) s) (s ⟨1, by omega⟩) = branchA hn s ∪ branchB hn s", DescribeRole.Theorem),
            Node("decl-4", "second_original", "second_original", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.second_original.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem second_original {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :\n    remaining (remaining (FiniteVertexDominationCollapse.faceSet\n      (noncover (show 0 < n by omega) s)) (point (by omega) s)) (s ⟨1, by omega⟩) =\n      insert {point (by omega) s} (branchA hn s ∪ branchB hn s)", DescribeRole.Theorem),
            Node("decl-5", "branchA_fixed", "branchA_fixed", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchA_fixed.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem branchA_fixed {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)\n    {a : Finset V} (ha : a ∈ branchA hn s) :\n    point (by omega) s ∉ a ∧ s ⟨1, by omega⟩ ∉ a ∧\n      s ⟨2, by omega⟩ ∈ a ∧ s ⟨n-1, by omega⟩ ∈ a", DescribeRole.Theorem),
            Node("decl-6", "branchB_fixed", "branchB_fixed", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchB_fixed.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem branchB_fixed {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)\n    {a : Finset V} (ha : a ∈ branchB hn s) :\n    point (by omega) s ∉ a ∧ s ⟨n-1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∉ a ∧\n      s ⟨1, by omega⟩ ∈ a ∧ s ⟨3, by omega⟩ ∈ a ∧ s ⟨n-2, by omega⟩ ∈ a", DescribeRole.Theorem),
            Node("decl-7", "IntervalIndependent", "IntervalIndependent", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.IntervalIndependent.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef IntervalIndependent {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)\n    (lo hi : Nat) (a : Finset V) : Prop", DescribeRole.Definition),
            Node("decl-8", "branchA_iff", "branchA_iff", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchA_iff.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem branchA_iff {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (a : Finset V) :\n    a ∈ branchA hn s ↔ a ⊆ ground s ∧ point (by omega) s ∉ a ∧\n      s ⟨1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∈ a ∧ s ⟨n-1, by omega⟩ ∈ a ∧\n        IntervalIndependent hn s 3 (n-1) a", DescribeRole.Theorem),
            Node("decl-9", "branchB_iff", "branchB_iff", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branchB_iff.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem branchB_iff {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (a : Finset V) :\n    a ∈ branchB hn s ↔ a ⊆ ground s ∧ point (by omega) s ∉ a ∧\n      s ⟨n-1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∉ a ∧ s ⟨1, by omega⟩ ∈ a ∧\n        s ⟨3, by omega⟩ ∈ a ∧ s ⟨n-2, by omega⟩ ∈ a ∧\n          IntervalIndependent hn s 4 (n-2) a", DescribeRole.Theorem),
            Node("decl-10", "second_noBranch_faces", "second_noBranch_faces", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.second_noBranch_faces.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem second_noBranch_faces {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :\n    (((nativeRelative (noncover (show 0 < n by omega) s)).noBranch\n      (point (by omega) s)).noBranch (s ⟨1, by omega⟩)).F = branchA hn s", DescribeRole.Theorem),
            Node("decl-11", "second_yesBranch_faces", "second_yesBranch_faces", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.second_yesBranch_faces.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem second_yesBranch_faces {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :\n    (((nativeRelative (noncover (show 0 < n by omega) s)).noBranch\n      (point (by omega) s)).yesBranch (s ⟨1, by omega⟩)).F = branchB hn s", DescribeRole.Theorem),
            Node("decl-12", "branch_survivors", "branch_survivors", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches.branch_survivors.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem branch_survivors {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (vs : List V)\n    (hvs : s ⟨1, by omega⟩ ∉ vs) :\n    survivors (remaining (tailFaces (by omega) s) (s ⟨1, by omega⟩)) vs =\n      survivors (branchA hn s) vs ∪ survivors (branchB hn s) vs", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title,
        string prose, string rawContract, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose), SourceText(rawContract)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
