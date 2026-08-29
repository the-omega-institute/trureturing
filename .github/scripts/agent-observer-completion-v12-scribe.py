from pathlib import Path
import json

entries = [
    {
        "path": "Blueprint/D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.scribe.cs",
        "namespace": "StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement",
        "class": "PostprocessingKernelCalculusDocument",
        "declaration": "D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.postprocessing_kernel_eq_iff_injOn_range",
        "describe_id": "postprocessing-kernel-calculus",
        "title": "Postprocessing Kernel Calculus",
        "abstract": "Postprocessing enlarges an observation kernel, with equality exactly when it is injective on the realized readout image.",
        "statement": "Realized-image injectivity characterizes exact kernel preservation",
        "comments": [
            "The theorem uses Set.InjOn on the realized range of the readout. Global injectivity on unused codomain values is intentionally unnecessary.",
            "Together with the companion strictness theorem, a realized collision is exactly the witness that postprocessing has destroyed an observable distinction."
        ],
        "formula": "Disp(Seq(F.Id(\"processed_kernel_equals_raw_kernel\"), Sp, Iff, Sp, F.Id(\"postprocess_injective_on_realized_range\"), Dot))"
    },
    {
        "path": "Blueprint/D5/S3/ObserverMemory/Refinement/JointReadoutSupremum.scribe.cs",
        "namespace": "StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement",
        "class": "JointReadoutSupremumDocument",
        "declaration": "D5/S3/ObserverMemory/Refinement/JointReadoutSupremum.pair_readout_kernel",
        "describe_id": "joint-readout-supremum",
        "title": "Joint Readout Supremum",
        "abstract": "A paired readout has the intersection kernel and supplies the supremum of its two coordinates in the refinement preorder.",
        "statement": "The joint-readout kernel is the intersection of the coordinate kernels",
        "comments": [
            "The paired interface records both readouts. Equality of pairs is therefore equivalent to simultaneous equality in both coordinates.",
            "The same module gives canonical projection refinements and the least-common-refinement factor, using the repository Refines structure rather than a parallel order."
        ],
        "formula": "Disp(Seq(F.Id(\"K_pair_q_s\"), Sp, Eq, Sp, F.Id(\"K_q_inter_K_s\"), Dot))"
    },
    {
        "path": "Blueprint/D5/S3/Observer/Agency/Self/AgencyEnrichment.scribe.cs",
        "namespace": "StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Self",
        "class": "AgencyEnrichmentDocument",
        "declaration": "D5/S3/Observer/Agency/Self/AgencyEnrichment.agency_enrichment_kernel_eq_current_iff_no_residual",
        "describe_id": "agency-enrichment",
        "title": "Agency Enrichment",
        "abstract": "Pairing current readout and strategy isolates the strategy residual inside each current-state fiber.",
        "statement": "Agency enrichment adds no distinction exactly when the strategy residual vanishes",
        "comments": [
            "Agency enrichment is the joint readout of current state and strategy. It is an interface supremum, without yet asserting dynamical closure.",
            "The strategy residual consists of pairs merged by the current readout and separated by strategy. Its vanishing is equivalent to factorization of strategy through the realized current image."
        ],
        "formula": "Disp(Seq(F.Id(\"K_agency_enrichment_equals_K_current\"), Sp, Iff, Sp, F.Id(\"strategy_residual_empty\"), Dot))"
    },
    {
        "path": "Blueprint/D5/S3/Observer/Agency/Holonomy/VisibleLoopHolonomy.scribe.cs",
        "namespace": "StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Holonomy",
        "class": "VisibleLoopHolonomyDocument",
        "declaration": "D5/S3/Observer/Agency/Holonomy/VisibleLoopHolonomy.visible_loop_policy_change_witnesses_pointed_holonomy",
        "describe_id": "visible-loop-holonomy",
        "title": "Visible Loop Holonomy",
        "abstract": "A strategy change along a visible loop certifies pointed holonomy: visible return together with nontrivial hidden transport.",
        "statement": "Strategy-visible drift on a visible loop witnesses pointed holonomy",
        "comments": [
            "A word is a visible loop only at a specified base state and relative to a specified readout. Nontrivial transport alone is not called holonomy.",
            "The conclusion packages both clauses: the visible readout returns while the hidden state fails to return. Strategy factorization through the visible readout makes every such loop strategy-invisible."
        ],
        "formula": "Disp(Seq(F.Id(\"visible_loop\"), Sp, Land, Sp, F.Id(\"strategy_changes\"), Sp, Rightarrow, Sp, F.Id(\"pointed_holonomy\"), Dot))"
    },
    {
        "path": "Blueprint/D5/S3/Observer/Completion/CompletionLocusCalculus.scribe.cs",
        "namespace": "StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion",
        "class": "CompletionLocusCalculusDocument",
        "declaration": "D5/S3/Observer/Completion/CompletionLocusCalculus.completion_locus_pair_eq_inter",
        "describe_id": "completion-locus-calculus",
        "title": "Completion Locus Calculus",
        "abstract": "Structural zero-defect completion loci compose by intersection and pull back exactly along parameter maps.",
        "statement": "Paired defects cut out the intersection of their completion loci",
        "comments": [
            "This is a parameter-space zero-locus calculus built on the canonical completionPointSet carrier.",
            "It is deliberately separate from behavior completion of an observation interface. The module also proves exact pullback and gauge-stability closure under conjunction."
        ],
        "formula": "Disp(Seq(F.Id(\"Z_paired_defect\"), Sp, Eq, Sp, F.Id(\"Z_first_inter_Z_second\"), Dot))"
    },
    {
        "path": "Blueprint/D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.scribe.cs",
        "namespace": "StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure",
        "class": "FiniteHorizonKernelRecurrenceDocument",
        "declaration": "D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.complete_kernel_eq_iInf_finite_horizon",
        "describe_id": "finite-horizon-kernel-recurrence",
        "title": "Finite-Horizon Kernel Recurrence",
        "abstract": "Finite behavior kernels descend one coordinate at a time and their infimum is the complete future-itinerary kernel.",
        "statement": "The complete kernel is the infimum of all finite-horizon kernels",
        "comments": [
            "The construction reuses futureReadoutWord and completeItinerary. No second behavior-completion carrier is introduced.",
            "A new terminal coordinate yields strict refinement exactly when it separates a pair surviving the previous horizon. On finite state spaces the canonical completionDepth already realizes the infinite kernel."
        ],
        "formula": "Disp(Seq(F.Id(\"K_complete\"), Sp, Eq, Sp, F.Id(\"infimum_m_K_m\"), Dot))"
    },
    {
        "path": "Blueprint/D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.scribe.cs",
        "namespace": "StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure",
        "class": "CommutingClosureCommonFixedPointDocument",
        "declaration": "D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.commuting_closure_composition_fixed_iff",
        "describe_id": "commuting-closure-common-fixed-point",
        "title": "Commuting Closure Common Fixed Point",
        "abstract": "Two commuting closure operators compose to a closure whose fixed points are exactly their common fixed points.",
        "statement": "Fixed points of the commuting composition are precisely common fixed points",
        "comments": [
            "Commutativity makes one pass sufficient and makes the composition independent of order.",
            "This theorem covers the binary commuting case. Arbitrary noncommuting closure families still require the transfinite common-fixed-point construction stated in the theory document."
        ],
        "formula": "Disp(Seq(F.Id(\"composite_fixes_x\"), Sp, Iff, Sp, F.Id(\"first_fixes_x_and_second_fixes_x\"), Dot))"
    },
]


def q(value: str) -> str:
    return json.dumps(value)


template = '''using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace {namespace};

internal sealed class {class_name} : IScribeDocumentDefinition
{{
    private const string Declaration = {declaration};

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        {abstract},
        H({title}),
        Blocks(Describe.Lean(
            DescribeId.Create({describe_id}),
            DeclarationHandle.Create(Declaration),
            H({statement}),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
{paragraphs}),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        {formula};
}}
'''

for entry in entries:
    paragraphs = ",\n".join(
        f"                Paragraph(Text({q(comment)}))" for comment in entry["comments"]
    )
    content = template.format(
        namespace=entry["namespace"],
        class_name=entry["class"],
        declaration=q(entry["declaration"]),
        abstract=q(entry["abstract"]),
        title=q(entry["title"]),
        describe_id=q(entry["describe_id"]),
        statement=q(entry["statement"]),
        paragraphs=paragraphs,
        formula=entry["formula"],
    )
    target = Path(entry["path"])
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8")
