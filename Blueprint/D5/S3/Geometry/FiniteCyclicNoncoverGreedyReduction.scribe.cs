using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

// Exact attempted source contracts; native Scribe acceptance is unobserved.
internal sealed class FiniteCyclicNoncoverGreedyReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FiniteCyclicNoncoverGreedyReduction source implementation.", H("FiniteCyclicNoncoverGreedyReduction"),
        Blocks(
            Paragraph(Text("The literal original NC(C_n) first round, native no/yes restrictions, direct injective label transport and genuine n=3/4/5 survivor bases. This does not assert the missing all-n congruence formulas or CriticalData. Lexical section variables are recorded faithfully. Lean may omit unused variables. Compiled telescopes, generated declarations and exact source-selector coordinates are unobserved. Native audit counts are zero.")),
            Node("decl-1", "TailIndependent", "TailIndependent", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.TailIndependent.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef TailIndependent {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) (a : Finset V) : Prop", DescribeRole.Definition),
            Node("decl-2", "tailFaces", "tailFaces", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.tailFaces.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef tailFaces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) : Finset (Finset V)", DescribeRole.Definition),
            Node("decl-3", "first_round", "first_round", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.first_round.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem first_round {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :\n    remaining (faceSet (noncover (show 0 < n by omega) s)) (point hn s) =\n      insert {point hn s} (tailFaces hn s)", DescribeRole.Theorem),
            Node("decl-4", "tail_omits_point", "tail_omits_point", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.tail_omits_point.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem tail_omits_point {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V)\n    {a : Finset V} (ha : a ∈ tailFaces hn s) : point hn s ∉ a", DescribeRole.Theorem),
            Node("decl-5", "first_noBranch_faces", "first_noBranch_faces", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.first_noBranch_faces.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem first_noBranch_faces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :\n    ((nativeRelative (noncover (show 0 < n by omega) s)).noBranch (point hn s)).F =\n      tailFaces hn s", DescribeRole.Theorem),
            Node("decl-6", "first_yesBranch_faces", "first_yesBranch_faces", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.first_yesBranch_faces.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem first_yesBranch_faces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :\n    ((nativeRelative (noncover (show 0 < n by omega) s)).yesBranch (point hn s)).F =\n      {{point hn s}}", DescribeRole.Theorem),
            Node("decl-7", "indexFaces", "indexFaces", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.indexFaces.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef indexFaces (n : Nat) (hn : 0 < n) : Finset (Finset (Fin n))", DescribeRole.Definition),
            Node("decl-8", "remainingFaces_map", "remainingFaces_map", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.remainingFaces_map.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remainingFaces_map {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :\n    remainingFaces hn s =\n      (computeSurvivors (indexFaces n (show 0 < n by omega)) (List.finRange n)).image\n        (Finset.map s)", DescribeRole.Theorem),
            Node("decl-9", "survivors_three", "survivors_three", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.survivors_three.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem survivors_three (s : Fin 3 ↪ V) :\n    remainingFaces (by omega) s =\n      insert {point (by omega) s} {criticalA 1 (by omega) s, criticalB 1 (by omega) s}", DescribeRole.Theorem),
            Node("decl-10", "survivors_four", "survivors_four", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.survivors_four.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem survivors_four (s : Fin 4 ↪ V) :\n    remainingFaces (by omega) s = insert {point (by omega) s} {criticalOne 1 s}", DescribeRole.Theorem),
            Node("decl-11", "survivors_five", "survivors_five", "Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.survivors_five.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem survivors_five (s : Fin 5 ↪ V) :\n    remainingFaces (by omega) s = insert {point (by omega) s} {criticalTwo 1 (by omega) s}", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title,
        string prose, string rawContract, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose)), Paragraph(Text(rawContract))), role);
}
