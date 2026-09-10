using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class TemplateShadowDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ten shadow registrations compare generated realizations with their hand registrations on canonical arenas.",
        H("Registration Shadows"),
        Blocks(
            Paragraph(Text("Each shadow retains unrestricted agreement-kernel equality, statement equality, nondegeneracy, a complete state enumeration, a law-sensitivity witness, and a separated state pair. The module seals the ten registrations and checks their finite-occurrence census queries.")),
            DeclarationNode("spectrum-realization", "spectrumRealization", "Spectrum shadow",
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
            DeclarationNode("intervention-realization", "interventionRealization", "Intervention shadow",
                "The separation template supplies intervention and counterfactual readouts on the canonical intervention arena."),
            DeclarationNode("observation-realization", "observationRealization", "Observation shadow",
                "The same separation template supplies observation and intervention readouts on the canonical observation-intervention arena."),
            DeclarationNode("agenda-realization", "agendaRealization", "Agenda shadow",
                "The admitted-surjection helper uses the sequential winner and agenda validity predicate."),
            DeclarationNode("preemption-realization", "preemptionRealization", "Preemption shadow",
                "The anchored-separation helper uses end state, active cause, ordered-preemption predicates, and the two source traces."),
            DeclarationNode("context-realization", "contextRealization", "Context shadow",
                "The context-selection helper uses the source interpretation parameters and its two fixed-meaning predicates."),
            DeclarationNode("static-realization", "staticRealization", "Static-design shadow",
                "The exact-design helper supplies the two Boolean readouts over Fin 3."),
            DeclarationNode("completion-realization", "completionRealization", "Completion shadow",
                "The completion-exchange helper uses the source counterexample transitions and readout."),
            DeclarationNode("gluing-realization", "gluingRealization", "Gluing shadow",
                "The scope-table helper supplies the three local equality and inequality predicates."),
            DeclarationNode("residue-realization", "residueRealization", "Adaptive residue shadow",
                "The two-step helper supplies residueReadout on the canonical residueArena."),
            DeclarationNode("residue-bridge", "residue_bridge", "Adaptive residue registration bridge",
                "The generic twoStepLegacy bridge preserves the full source statement, including history-dependent questions and minimum costs.", DescribeRole.Theorem),
            DeclarationNode("residue-kernel-equality", "residue_kernel_equal", "Residue agreement kernels coincide",
                "For every pair of states, the generated bundle agrees exactly when the hand bundle agrees.", DescribeRole.Theorem),
            DeclarationNode("residue-nondegenerate", "residue_nondegenerate", "Nondegenerate residue arena",
                "The canonical arena contains distinct states.", DescribeRole.Theorem),
            DeclarationNode("residue-enumeration", "residueEnumeration", "Complete residue enumeration",
                "The shadow uses the canonical arena's complete state enumeration."),
            DeclarationNode("residue-law-sensitive", "residue_lawSensitive", "Residue law sensitivity",
                "The source realization satisfies the law; the constant-false sensor family does not.", DescribeRole.Theorem),
            Paragraph(Text("The library contains one reused template, separation, and eight single-consumer helpers. The two-step helper transports Nat.find minima and preserves the higher-order binary protocol law. All ten shadows participate in the shared seal and certified finite-occurrence census queries.")))));

    private static DocumentBlock.Describe DeclarationNode(
        string id, string declaration, string title, string paragraph,
        DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            role);

    private static Formula Agreement(string bundle) => Seq(
        Operatorname, Grp(F.Id("agrees")), Open, F.Id(bundle), Comma, Sp,
        F.Id("x"), Comma, Sp, F.Id("y"), Close);
}
