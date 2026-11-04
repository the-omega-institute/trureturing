using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LayeredCirculation;

internal sealed class SupplierGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The necessary finite typed-walk and real flow interface is a licensed source transplant from elazarg/multitubes at commit 20d22aa7ca67f9843e5adf9edf173403a2f4033a. The original proof source is identified in the Lean license notice. These helpers are consumed by the real layered local-law theorem; no new mathematical novelty is attributed to the supplier.",
        H("SupplierGraph"),
        Blocks(
            Paragraph(Text("Generic declarations use these source contexts: universe uV uE variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E) variable {G} {start finish middle : V} universe uV uE variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E) variable {G} {start finish : V} universe uV uE variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E} {start finish : V}")),
            Describe.Lean(
                DescribeId.Create("length"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length"),
                H("length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] def length {start : V} : {finish : V} → G.Walk start finish → ℕ | _, .nil => 0 | _, .concat walkSoFar _ _ => walkSoFar.length + 1"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edges"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges"),
                H("edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def edges {start : V} : {finish : V} → G.Walk start finish → List E | _, .nil => [] | _, .concat walkSoFar edge _ => walkSoFar.edges ++ [edge]"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("length-concat"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_concat"),
                H("length concat"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem length_concat (walkSoFar : G.Walk start finish) (edge : E) (legal : G.source edge = finish) : (Walk.concat walkSoFar edge legal).length = walkSoFar.length + 1"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edges-concat"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_concat"),
                H("edges concat"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_concat (walkSoFar : G.Walk start finish) (edge : E) (legal : G.source edge = finish) : (Walk.concat walkSoFar edge legal).edges = walkSoFar.edges ++ [edge]"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edges-length"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_length"),
                H("edges length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_length (walk : G.Walk start finish) : walk.edges.length = walk.length"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visited"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.visited"),
                H("visited"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def visited {start : V} : {finish : V} → G.Walk start finish → List V | _, .nil => [start] | _, .concat walkSoFar edge _ => walkSoFar.visited ++ [G.target edge]"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("length-visited"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_visited"),
                H("length visited"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem length_visited (walk : G.Walk start finish) : walk.visited.length = walk.length + 1"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mem-visited-of-mem-edges"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.mem_visited_of_mem_edges"),
                H("mem visited of mem edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem mem_visited_of_mem_edges (walk : G.Walk start finish) {edge : E} (hmem : edge ∈ walk.edges) : G.target edge ∈ walk.visited"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edges-nodup-of-visited-nodup"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_nodup_of_visited_nodup"),
                H("edges nodup of visited nodup"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem edges_nodup_of_visited_nodup (walk : G.Walk start finish) (hnd : walk.visited.Nodup) : walk.edges.Nodup"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-split-of-mem-visited"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_split_of_mem_visited"),
                H("exists split of mem visited"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem exists_split_of_mem_visited (walk : G.Walk start finish) {vertex : V} (hmem : vertex ∈ walk.visited) : ∃ (before : G.Walk start vertex) (after : G.Walk vertex finish), walk.edges = before.edges ++ after.edges"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-closedsubwalk-of-not-nodup"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_closedSubwalk_of_not_nodup"),
                H("exists closedSubwalk of not nodup"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem exists_closedSubwalk_of_not_nodup (walk : G.Walk start finish) (hdup : ¬ walk.visited.Nodup) : ∃ (vertex : V) (before : G.Walk start vertex) (cycle : G.Walk vertex vertex) (after : G.Walk vertex finish), 0 < cycle.length ∧ walk.edges = before.edges ++ cycle.edges ++ after.edges"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edges-ischain"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_isChain"),
                H("edges isChain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem edges_isChain (walk : G.Walk start finish) : walk.edges.IsChain fun first second => G.target first = G.source second"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-head"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.source_head"),
                H("source head"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem source_head (walk : G.Walk start finish) (hne : walk.edges ≠ []) : G.source (walk.edges.head hne) = start"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-getlast"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.target_getLast"),
                H("target getLast"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem target_getLast (walk : G.Walk start finish) (hne : walk.edges ≠ []) : G.target (walk.edges.getLast hne) = finish"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edgemultiplicity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity"),
                H("edgeMultiplicity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] def edgeMultiplicity [DecidableEq E] {start : V} : {finish : V} → G.Walk start finish → E → ℕ | _, .nil => fun _ => 0 | _, .concat walkSoFar edge _ => fun candidate => walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edgemultiplicity-pos-iff-mem-edges"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_pos_iff_mem_edges"),
                H("edgeMultiplicity pos iff mem edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem edgeMultiplicity_pos_iff_mem_edges [DecidableEq E] (walk : G.Walk start finish) (edge : E) : 0 < walk.edgeMultiplicity edge ↔ edge ∈ walk.edges"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edgemultiplicity-eq-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_eq_count"),
                H("edgeMultiplicity eq count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem edgeMultiplicity_eq_count [DecidableEq E] (walk : G.Walk start finish) (edge : E) : walk.edgeMultiplicity edge = walk.edges.count edge"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edgemultiplicity-eq-one-iff-mem-edges"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_eq_one_iff_mem_edges"),
                H("edgeMultiplicity eq one iff mem edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem edgeMultiplicity_eq_one_iff_mem_edges [DecidableEq E] (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) : walk.edgeMultiplicity edge = 1 ↔ edge ∈ walk.edges"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("castfinish"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.castFinish"),
                H("castFinish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def castFinish {start finish finish' : V} (walk : G.Walk start finish) (hfinish : finish = finish') : G.Walk start finish' := hfinish ▸ walk"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("length-castfinish"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_castFinish"),
                H("length castFinish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem length_castFinish {start finish finish' : V} (walk : G.Walk start finish) (hfinish : finish = finish') : (walk.castFinish hfinish).length = walk.length"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edges-castfinish"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_castFinish"),
                H("edges castFinish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_castFinish {start finish finish' : V} (walk : G.Walk start finish) (hfinish : finish = finish') : (walk.castFinish hfinish).edges = walk.edges"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("caststart"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.castStart"),
                H("castStart"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def castStart {start start' finish : V} (walk : G.Walk start finish) (hstart : start = start') : G.Walk start' finish := hstart ▸ walk"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("length-caststart"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_castStart"),
                H("length castStart"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem length_castStart {start start' finish : V} (walk : G.Walk start finish) (hstart : start = start') : (walk.castStart hstart).length = walk.length"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edges-caststart"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_castStart"),
                H("edges castStart"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_castStart {start start' finish : V} (walk : G.Walk start finish) (hstart : start = start') : (walk.castStart hstart).edges = walk.edges"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("append"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.append"),
                H("append"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] def append {start middle : V} (first : G.Walk start middle) : {finish : V} → G.Walk middle finish → G.Walk start finish | _, .nil => first | _, .concat second edge legal => .concat (first.append second) edge legal"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edges-append"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edges_append"),
                H("edges append"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem edges_append (first : G.Walk start middle) (second : G.Walk middle finish) : (first.append second).edges = first.edges ++ second.edges"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("length-append"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.length_append"),
                H("length append"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: @[simp] theorem length_append (first : G.Walk start middle) (second : G.Walk middle finish) : (first.append second).length = first.length + second.length"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("outgoingmultiplicity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.outgoingMultiplicity"),
                H("outgoingMultiplicity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def outgoingMultiplicity [Fintype E] [DecidableEq V] (multiplicity : E → ℕ) (vertex : V) : ℕ := ∑ edge with G.source edge = vertex, multiplicity edge"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("outgoing-multiplicity-concat"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.outgoingMultiplicity_edgeMultiplicity_concat"),
                H("Outgoing multiplicity after appending an edge"),
                StatementSource.FromAuthor(Disp(OutgoingMultiplicityConcatFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Appending a legal edge increases the outgoing multiplicity at a vertex "
                        + "by one exactly when that vertex is the edge source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("incomingmultiplicity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.incomingMultiplicity"),
                H("incomingMultiplicity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def incomingMultiplicity [Fintype E] [DecidableEq V] (multiplicity : E → ℕ) (vertex : V) : ℕ := ∑ edge with G.target edge = vertex, multiplicity edge"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edgemultiplicity-balanced"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.edgeMultiplicity_balanced"),
                H("edgeMultiplicity balanced"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem edgeMultiplicity_balanced [Fintype E] [DecidableEq E] [DecidableEq V] {base : V} (walk : G.Walk base base) (vertex : V) : G.outgoingMultiplicity walk.edgeMultiplicity vertex = G.incomingMultiplicity walk.edgeMultiplicity vertex"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.singleton"),
                H("singleton"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def singleton (edge : E) : G.Walk (G.source edge) (G.target edge) := .concat .nil edge rfl"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exists-splitatedge"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph.exists_splitAtEdge"),
                H("exists splitAtEdge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem exists_splitAtEdge (walk : G.Walk start finish) (edge : E) (hmem : edge ∈ walk.edges) : ∃ (before : G.Walk start (G.source edge)) (after : G.Walk (G.target edge) finish), walk.edges = before.edges ++ edge :: after.edges"))),
                DescribeRole.Theorem))));

    private static Formula OutgoingMultiplicityConcatFormula()
    {
        Formula source = At(Q("Maths", "EdgeGraph", "source"), X("G"), X("edge"));
        Formula appended = At(Q("Maths", "EdgeGraph", "Walk", "concat"),
            X("walk"), X("edge"), X("legal"));
        Formula Multiplicity(Formula walk) => At(
            Q("Maths", "EdgeGraph", "outgoingMultiplicity"), X("G"),
            At(Q("Maths", "EdgeGraph", "Walk", "edgeMultiplicity"), walk), X("vertex"));
        Formula indicator = At(Q("ite"), Equal(source, X("vertex")), D(1), D(0));
        Formula body = Equal(Multiplicity(appended), new Formula.Binary(
            Multiplicity(X("walk")), FormulaBinaryOperator.Add, indicator));
        (string Name, Formula Type)[] binders =
        [
            ("V", Q("Type")), ("E", Q("Type")),
            ("G", At(Q("Maths", "EdgeGraph"), X("V"), X("E"))),
            ("start", X("V")), ("finish", X("V")),
            ("", At(Q("Fintype"), X("E"))),
            ("", At(Q("DecidableEq"), X("E"))),
            ("", At(Q("DecidableEq"), X("V"))),
            ("walk", At(Q("Maths", "EdgeGraph", "Walk"), X("G"), X("start"), X("finish"))),
            ("edge", X("E")), ("legal", Equal(source, X("finish"))), ("vertex", X("V"))
        ];
        for (int i = binders.Length - 1; i >= 0; i--)
            body = binders[i].Name.Length == 0
                ? Seq(OpenBracket, binders[i].Type, CloseBracket, Sp, body)
                : All(binders[i].Name, binders[i].Type, body);
        return body;
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (string name in names)
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Par(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Par(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Par(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

}
