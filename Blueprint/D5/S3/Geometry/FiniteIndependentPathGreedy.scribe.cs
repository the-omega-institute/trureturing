using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteIndependentPathGreedyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteIndependentPathGreedy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/FiniteIndependentPathGreedy",
            "Augmented independent paths have an exact unbounded three-coordinate greedy recurrence.",
            "augmented-path-greedy-recurrence",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Data.List.Nodup")), H("FiniteIndependentPathGreedy"),
        Blocks(
            Paragraph(Text("The full augmented path family and an unbounded three-coordinate survivor recurrence, with distinct 0/1/2 bases, literal insertion transport, a modulo-three closed recursive selection, and independent-path membership. Lexical section variables are recorded faithfully. Lean may omit unused variables.")),
            Node("decl-1", "paths", "paths", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.paths.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef paths : List V → Finset (Finset V)", DescribeRole.Definition),
            Node("decl-2", "remaining_paths_three", "remaining_paths_three", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.remaining_paths_three.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_paths_three (v w z : V) (vs : List V)\n    (hd : (v :: w :: z :: vs).Nodup) :\n    remaining (paths (v :: w :: z :: vs)) v = (paths vs).image (insert w)", DescribeRole.Theorem),
            Node("decl-3", "remaining_paths_two", "remaining_paths_two", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.remaining_paths_two.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_paths_two (v w : V) (hvw : v ≠ w) :\n    remaining (paths [v, w]) v = {{w}}", DescribeRole.Theorem),
            Node("decl-4", "remaining_paths_one", "remaining_paths_one", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.remaining_paths_one.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_paths_one (v : V) : remaining (paths [v]) v = ∅", DescribeRole.Theorem),
            Node("decl-5", "pathCritical", "pathCritical", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.pathCritical.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef pathCritical : List V → Finset (Finset V)", DescribeRole.Definition),
            Node("decl-6", "survivors_paths", "survivors_paths", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.survivors_paths.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem survivors_paths (vs : List V) (hd : vs.Nodup) :\n    survivors (paths vs) vs = pathCritical vs", DescribeRole.Theorem),
            Node("decl-7", "pathChosen", "pathChosen", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.pathChosen.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef pathChosen : List V → Finset V", DescribeRole.Definition),
            Node("decl-8", "survivors_paths_closed", "survivors_paths_closed", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.survivors_paths_closed.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem survivors_paths_closed (vs : List V) (hd : vs.Nodup) :\n    survivors (paths vs) vs =\n      if vs.length % 3 = 1 then ∅ else {pathChosen vs}", DescribeRole.Theorem),
            Node("decl-9", "IndependentAlong", "IndependentAlong", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.IndependentAlong.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ndef IndependentAlong : List V → Finset V → Prop", DescribeRole.Definition),
            Node("decl-10", "mem_paths_iff", "mem_paths_iff", "Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.mem_paths_iff.", "Lexical source context (not a compiled telescope):\nvariable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem mem_paths_iff (vs : List V) (hd : vs.Nodup) (a : Finset V) :\n    a ∈ paths vs ↔ (∀ x ∈ a, x ∈ vs) ∧ IndependentAlong vs a", DescribeRole.Theorem))));

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
