using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class TemplateShadowDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine shadow registrations compare generated realizations with their hand registrations on canonical arenas.",
        H("Registration Shadows"),
        Blocks(
            Paragraph(Text("Each shadow retains unrestricted agreement-kernel equality, statement equality, nondegeneracy, a complete state enumeration, a law-sensitivity witness, and a separated state pair. The module seals the nine registrations and checks their finite-occurrence census queries.")),
            DefinitionNode("spectrum-realization", "spectrumRealization", "Spectrum shadow",
                "The bijection helper uses SpectrumAtom.index on the canonical spectrum arena."),
            Describe.Lean(
                DescribeId.Create("spectrum-kernel-equality"),
                DeclarationHandle.Create(Prefix + "spectrum_kernel_equal"),
                H("Spectrum agreement kernels coincide"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp,
                    Agreement("shadow"), Sp, Iff, Sp, Agreement("hand"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here shadow denotes spectrumRealization.toPrimitiveBundle and hand denotes FirstThreeRealizations.spectrumRealization.toPrimitiveBundle. The equivalence holds for every pair of states."))),
                DescribeRole.Theorem),
            DefinitionNode("intervention-realization", "interventionRealization", "Intervention shadow",
                "The separation template supplies intervention and counterfactual readouts on the canonical intervention arena."),
            DefinitionNode("observation-realization", "observationRealization", "Observation shadow",
                "The same separation template supplies observation and intervention readouts on the canonical observation-intervention arena."),
            DefinitionNode("agenda-realization", "agendaRealization", "Agenda shadow",
                "The admitted-surjection helper uses the sequential winner and agenda validity predicate."),
            DefinitionNode("preemption-realization", "preemptionRealization", "Preemption shadow",
                "The anchored-separation helper uses end state, active cause, ordered-preemption predicates, and the two source traces."),
            DefinitionNode("context-realization", "contextRealization", "Context shadow",
                "The context-selection helper uses the source interpretation parameters and its two fixed-meaning predicates."),
            DefinitionNode("static-realization", "staticRealization", "Static-design shadow",
                "The exact-design helper supplies the two Boolean readouts over Fin 3."),
            DefinitionNode("completion-realization", "completionRealization", "Completion shadow",
                "The completion-exchange helper uses the source counterexample transitions and readout."),
            DefinitionNode("gluing-realization", "gluingRealization", "Gluing shadow",
                "The scope-table helper supplies the three local equality and inequality predicates."),
            Paragraph(Text("Only separation meets the two-instance reuse criterion; the other seven families are helpers. Adaptive residue identification remains outside this pack: its law includes noncomputable minimum depths and higher-order protocols. A future template needs a source-depth transport lemma preserving that protocol law; the Lean module's route-out comment identifies the exact declarations.")))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula Agreement(string bundle) => Seq(
        Operatorname, Grp(F.Id("agrees")), Open, F.Id(bundle), Comma, Sp,
        F.Id("x"), Comma, Sp, F.Id("y"), Close);
}
