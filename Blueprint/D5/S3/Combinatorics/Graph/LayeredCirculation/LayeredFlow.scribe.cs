using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LayeredCirculation;

internal sealed class LayeredFlowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five patterns are ordered 000,100,010,001,101 and the three seam states are 00,01,10. A local law has arbitrary real nonnegative coordinates, one unit of mass at each position, and all four binary-pair overlap equations, including the zero 11 equation. The graph vertices are ZMod n times Fin 3 and edges are ZMod n times Fin 5. Its conservation laws use the actual source and target labels. Native bridges transport the exact upstream signed real decomposition to forward circuits, identify their winding numbers, and certify strict positive-support erasure.",
        H("LayeredFlow"),
        Blocks(
            Paragraph(Text("Generic declarations use these source contexts:")),
            Describe.Lean(
                DescribeId.Create("pattern"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.pattern"),
                H("pattern"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def pattern : Fin 5 → Bool × Bool × Bool := ![(false, false, false), (true, false, false), (false, true, false), (false, false, true), (true, false, true)]"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("seam"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.seam"),
                H("seam"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def seam : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sourcestate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.sourceState"),
                H("sourceState"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def sourceState : Fin 5 → Fin 3 := ![0, 2, 1, 0, 2]"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("targetstate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.targetState"),
                H("targetState"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def targetState : Fin 5 → Fin 3 := ![0, 0, 2, 1, 1]"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("islocallaw"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.IsLocalLaw"),
                H("IsLocalLaw"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def IsLocalLaw {n : ℕ} (p : ZMod n → Fin 5 → ℝ) : Prop := (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ = 1) ∧ ∀ i b c, (∑ σ, if (pattern σ).2.1 = b ∧ (pattern σ).2.2 = c then p i σ else 0) = ∑ σ, if (pattern σ).1 = b ∧ (pattern σ).2.1 = c then p (i + 1) σ else 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("localscore"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.localScore"),
                H("localScore"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def localScore {n : ℕ} [NeZero n] (f p : ZMod n → Fin 5 → ℝ) : ℝ := ∑ i, ∑ σ, f i σ * p i σ"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("layeredgraph"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layeredGraph"),
                H("layeredGraph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def layeredGraph (n : ℕ) : EdgeGraph (ZMod n × Fin 3) (ZMod n × Fin 5) where source e := (e.1, sourceState e.2) target e := (e.1 + 1, targetState e.2)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("labels"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.labels"),
                H("labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem labels (σ : Fin 5) : seam (sourceState σ) = ((pattern σ).1, (pattern σ).2.1) ∧ seam (targetState σ) = ((pattern σ).2.1, (pattern σ).2.2)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("iscirculation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.IsCirculation"),
                H("IsCirculation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def IsCirculation {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Prop := ∀ v, (∑ e, if (layeredGraph n).source e = v then p e.1 e.2 else 0) = ∑ e, if (layeredGraph n).target e = v then p e.1 e.2 else 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-law-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_law_iff"),
                H("local law iff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem local_law_iff {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : IsLocalLaw p ↔ (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ = 1) ∧ IsCirculation p"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("layercount"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layerCount"),
                H("layerCount"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def layerCount {n : ℕ} {a b : ZMod n × Fin 3} (w : (layeredGraph n).Walk a b) (i : ZMod n) : ℕ := ∑ σ, w.edgeMultiplicity (i,σ)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("layer-count-uniform"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.layer_count_uniform"),
                H("layer count uniform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem layer_count_uniform {n : ℕ} [NeZero n] {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) (i : ZMod n) : layerCount w i = layerCount w 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("length-eq-layer-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.length_eq_layer_count"),
                H("length eq layer count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem length_eq_layer_count {n : ℕ} [NeZero n] {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) : w.length = n * layerCount w 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("walklaw"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walkLaw"),
                H("walkLaw"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def walkLaw {n : ℕ} {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) : ZMod n → Fin 5 → ℝ := fun i σ => w.edgeMultiplicity (i,σ) / layerCount w 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("walk-law-local"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walk_law_local"),
                H("walk law local"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem walk_law_local {n : ℕ} [NeZero n] {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) (hw : 0 < w.length) : IsLocalLaw (walkLaw w)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("walk-law-score"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.walk_law_score"),
                H("walk law score"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem walk_law_score {n : ℕ} [NeZero n] (f : ZMod n → Fin 5 → ℝ) {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) : localScore f (walkLaw w) = Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w / layerCount w 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-coefficient-forward"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_coefficient_forward"),
                H("Positive coefficients use only forward edges"),
                StatementSource.FromAuthor(Disp(PositiveCoefficientForwardFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a nonnegative simple-circuit decomposition whose reverse coefficients vanish, "
                        + "every edge of a positive-weight circuit has forward orientation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cycle-initial-visited-nodup"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.cycle_initial_visited_nodup"),
                H("No repeated vertex before the closing edge"),
                StatementSource.FromAuthor(Disp(CycleInitialVisitedNodupFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A cycle that has no proper positive closed subwalk visits each vertex "
                        + "at most once before its closing edge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simple-cycle-winding"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.simple_cycle_winding"),
                H("simple cycle winding"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem simple_cycle_winding {n : ℕ} [NeZero n] {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) (hw : IsSimpleCycle w) : 1 ≤ layerCount w 0 ∧ layerCount w 0 ≤ 3 ∧ w.length = n * layerCount w 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-simple-cycle-decomposition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_simple_cycle_decomposition"),
                H("local simple cycle decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem local_simple_cycle_decomposition {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) (hp : IsLocalLaw p) : ∃ (ι : Type) (_ : Fintype ι) (weight : ι → ℝ) (base : ι → ZMod n × Fin 3) (cycle : ∀ i, (layeredGraph n).Walk (base i) (base i)), (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i) = 1 ∧ (∀ i, 0 < weight i → IsSimpleCycle (cycle i)) ∧ (∀ i, 0 < weight i → 1 ≤ layerCount (cycle i) 0 ∧ layerCount (cycle i) 0 ≤ 3) ∧ (∀ i, 0 < weight i → IsLocalLaw (walkLaw (cycle i))) ∧ (∀ j σ, p j σ = ∑ i, weight i * walkLaw (cycle i) j σ) ∧ ∀ i, weight i = layerCount (cycle i) 0 * (weight i / layerCount (cycle i) 0)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positivesupport"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positiveSupport"),
                H("positiveSupport"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def positiveSupport {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Finset (ZMod n × Fin 5) := Finset.univ.filter (fun e => 0 < p e.1 e.2)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subtractcycle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.subtractCycle"),
                H("subtractCycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def subtractCycle {n : ℕ} {a : ZMod n × Fin 3} (p : ZMod n → Fin 5 → ℝ) (w : (layeredGraph n).Walk a a) (α : ℝ) : ZMod n → Fin 5 → ℝ := fun i σ => p i σ - α * w.edgeMultiplicity (i,σ)"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-cycle-erasure"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_cycle_erasure"),
                H("positive cycle erasure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem positive_cycle_erasure {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) (hnonneg : ∀ i σ, 0 ≤ p i σ) (hbal : IsCirculation p) (hne : p ≠ 0) : ∃ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a) (α : ℝ), IsSimpleCycle w ∧ 0 < α ∧ (∀ e ∈ w.edges, α ≤ p e.1 e.2) ∧ (∃ e ∈ w.edges, p e.1 e.2=α) ∧ (∀ i σ, 0 ≤ subtractCycle p w α i σ) ∧ IsCirculation (subtractCycle p w α) ∧ (positiveSupport (subtractCycle p w α)).card < (positiveSupport p).card ∧ ∀ e, (w.edgeMultiplicity e : ℝ) = if e ∈ w.edges then 1 else 0"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("haspositivecycledecomposition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.HasPositiveCycleDecomposition"),
                H("HasPositiveCycleDecomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def HasPositiveCycleDecomposition {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Prop := ∃ (ι : Type) (_ : Fintype ι) (base : ι → ZMod n × Fin 3) (cycle : ∀ i, (layeredGraph n).Walk (base i) (base i)) (α : ι → ℝ), (∀ i, IsSimpleCycle (cycle i) ∧ 0 < α i ∧ 1 ≤ layerCount (cycle i) 0 ∧ layerCount (cycle i) 0 ≤ 3 ∧ IsLocalLaw (walkLaw (cycle i)) ∧ (cycle i).length=layerCount (cycle i) 0 * n ∧ (∀ j, layerCount (cycle i) j=layerCount (cycle i) 0) ∧ ∀ e, ((cycle i).edgeMultiplicity e : ℝ) = if e ∈ (cycle i).edges then 1 else 0) ∧ (∑ i, (layerCount (cycle i) 0 : ℝ) * α i) = 1 ∧ (∀ j σ, p j σ = ∑ i, α i * (if (j,σ) ∈ (cycle i).edges then 1 else 0)) ∧ ∀ j σ, p j σ = ∑ i, ((layerCount (cycle i) 0 : ℝ) * α i) * walkLaw (cycle i) j σ"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-cycle-decomposition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.positive_cycle_decomposition"),
                H("positive cycle decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem positive_cycle_decomposition {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) (hp : IsLocalLaw p) : HasPositiveCycleDecomposition p"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("haspositivecycleerasure"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.HasPositiveCycleErasure"),
                H("HasPositiveCycleErasure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def HasPositiveCycleErasure {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Prop := ∃ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a) (α : ℝ), IsSimpleCycle w ∧ 0 < α ∧ (∀ e ∈ w.edges, α ≤ p e.1 e.2) ∧ (∃ e ∈ w.edges, p e.1 e.2=α) ∧ (∀ i σ, 0 ≤ subtractCycle p w α i σ) ∧ IsCirculation (subtractCycle p w α) ∧ (positiveSupport (subtractCycle p w α)).card < (positiveSupport p).card ∧ ∀ e, (w.edgeMultiplicity e : ℝ) = if e ∈ w.edges then 1 else 0"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-law-compact"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow.local_law_compact"),
                H("local law compact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem local_law_compact {n : ℕ} [NeZero n] : IsCompact {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p}"))),
                DescribeRole.Theorem))));

    private static Formula CycleInitialVisitedNodupFormula()
    {
        Formula target = At(Q("Maths", "EdgeGraph", "target"), X("G"), X("edge"));
        Formula source = At(Q("Maths", "EdgeGraph", "source"), X("G"), X("edge"));
        Formula Walk(Formula start, Formula finish) =>
            At(Q("Maths", "EdgeGraph", "Walk"), X("G"), start, finish);
        Formula Edges(string walk) => At(Q("Maths", "EdgeGraph", "Walk", "edges"), X(walk));
        Formula Length(string walk) => At(Q("Maths", "EdgeGraph", "Walk", "length"), X(walk));
        Formula Positive(Formula value) =>
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, value);
        Formula concat = At(Q("Maths", "EdgeGraph", "Walk", "concat"),
            X("initial"), X("edge"), X("legal"));
        Formula split = Equal(At(Q("Maths", "EdgeGraph", "Walk", "edges"), concat),
            At(Q("List", "append"),
                At(Q("List", "append"), Edges("before"), Edges("inner")), Edges("after")));
        Formula outside = new Formula.Binary(Length("before"), FormulaBinaryOperator.Add,
            Length("after"));
        Formula minimal = All("v", X("V"),
            All("before", Walk(target, X("v")),
            All("inner", Walk(X("v"), X("v")),
            All("after", Walk(X("v"), target),
                Imp(split, Imp(Positive(Length("inner")), Imp(Positive(outside), Q("False"))))))));
        Formula conclusion = At(Q("List", "Nodup"),
            At(Q("Maths", "EdgeGraph", "Walk", "visited"), X("initial")));
        return All("V", Q("Type"), All("E", Q("Type"),
            All("G", At(Q("Maths", "EdgeGraph"), X("V"), X("E")),
            All("a", X("V"), All("edge", X("E"), All("initial", Walk(target, X("a")),
            All("legal", Equal(source, X("a")), Imp(minimal, conclusion))))))));
    }

    private static Formula PositiveCoefficientForwardFormula()
    {
        Formula real = Seq(Mathbb, Grp(X("R")));
        Formula signedEdge = At(Q("Maths", "AdditiveTransport", "SignedEdge"), X("E"));
        Formula signedGraph = At(Q("Maths", "AdditiveTransport", "signedGraph"), X("G"));
        Formula ci = At(X("cycle"), X("i"));
        Formula edges = At(Q("Maths", "EdgeGraph", "Walk", "edges"), ci);
        Formula forward = Equal(At(Q("Prod", "snd"), X("e")), Q("Bool", "false"));
        Formula conclusion = All("e", signedEdge,
            Imp(new Formula.Relation(X("e"), FormulaRelationOperator.MemberOf, edges), forward));
        Formula positive = new Formula.Relation(Typed(D(0), real),
            FormulaRelationOperator.LessThan, At(X("weight"), X("i")));
        Formula zeroReverse = All("e", X("E"), Equal(
            At(X("coefficient"), At(Q("Prod", "mk"), X("e"), Q("Bool", "true"))),
            Typed(D(0), real)));
        Formula summand = new Formula.Binary(At(X("weight"), X("j")),
            FormulaBinaryOperator.Multiply,
            At(Q("Maths", "AdditiveTransport", "circuitCoefficient"),
                At(X("cycle"), X("j")), X("e")));
        Formula sum = At(Q("Finset", "sum"),
            Typed(Q("Finset", "univ"), At(Q("Finset"), X("J"))),
            Seq(LambdaLower, Sp, Typed(X("j"), X("J")), Sp, Mapsto, Sp, Par(summand)));
        Formula representation = All("e", signedEdge, Equal(At(X("coefficient"), X("e")), sum));
        Formula simple = All("i", X("J"),
            At(Q("Maths", "AdditiveTransport", "IsSimpleCycle"), ci));
        Formula nonnegative = All("i", X("J"), new Formula.Relation(Typed(D(0), real),
            FormulaRelationOperator.LessThanOrEqual, At(X("weight"), X("i"))));
        Formula walks = All("i", X("J"), At(Q("Maths", "EdgeGraph", "Walk"),
            signedGraph, At(X("base"), X("i")), At(X("base"), X("i"))));
        Formula body = Imp(nonnegative, Imp(simple, Imp(representation,
            Imp(zeroReverse, All("i", X("J"), Imp(positive, conclusion))))));
        (string Name, Formula Type)[] binders =
        [
            ("V", Q("Type")), ("E", Q("Type")), ("J", Q("Type")),
            ("", At(Q("Fintype"), X("E"))),
            ("", At(Q("DecidableEq"), X("E"))),
            ("", At(Q("Fintype"), X("J"))),
            ("G", At(Q("Maths", "EdgeGraph"), X("V"), X("E"))),
            ("coefficient", Arrow(signedEdge, real)),
            ("weight", Arrow(X("J"), real)), ("base", Arrow(X("J"), X("V"))),
            ("cycle", walks)
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
    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(Par(source), Par(target));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
}
