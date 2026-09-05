using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class CountingReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/CountingReflection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict list fold reflects finite state censuses into the frozen escape-count API.",
        H("Strict Counting Reflection"),
        Blocks(
            Def("state-enumeration", "StateEnumeration", "Complete state enumeration",
                "A duplicate-free state list is certified to contain the whole finite arena."),
            Def("index-enumeration", "IndexEnumeration", "Complete index enumeration",
                "A duplicate-free index list carries pointwise completeness."),
            Def("finite-index-enumeration", "finIndexEnumeration",
                "Canonical finite-index enumeration",
                "The ascending finite range enumerates every element of Fin n."),
            Def("list-unique-capture-summary", "ListUniqueCaptureSummary",
                "Strict counting summary",
                "Three census totals and fifteen nonzero role-mask buckets form one " +
                    "strict value."),
            Def("summary-bucket", "bucket", "Summary bucket selector",
                "A zero-based Fin 15 index selects the corresponding nonzero role-mask bucket."),
            Def("role-signature-of-bucket", "roleSignatureOfBucket",
                "Bucket role signature",
                "Bucket bits are decoded high-first in CUT, FLOW, ADMIT, ANCHOR order."),
            Def("list-unique-capture-summary-fold", "listUniqueCaptureSummary",
                "One-pass reflected census",
                "A strict nested fold classifies every ordered pair exactly once."),
            Thm("list-full-count-correct", "listFullEscapeCount_eq_escapeNumerator",
                "Reflected full count is exact", FullCountCorrect()),
            Thm("list-without-count-correct", "listWithoutEscapeCount_eq_escapeNumerator",
                "Reflected leave-one-out count is exact", WithoutCountCorrect()),
            Thm("list-unique-count-correct", "listUniqueCaptureCount_eq_uniqueCaptureCount",
                "Reflected unique count is exact", UniqueCountCorrect()),
            Thm("list-bucket-correct", "listBucket_eq_roleHistogram",
                "Reflected role buckets are exact", BucketCorrect()),
            Thm("unique-count-positive-transport", "uniqueCaptureCount_pos_of_list",
                "Reflected positivity transports", PositivityTransport()),
            Enumeration("agenda-state-enumeration", "Agenda-power state enumeration",
                "FirstThreeArenas.agendaPowerArena", "agendaPowerArena"),
            Enumeration("residue-state-enumeration", "Adaptive-residue state enumeration",
                "FirstThreeArenas.residueArena", "residueArena"),
            Enumeration("spectrum-state-enumeration", "Spectrum state enumeration",
                "FirstThreeArenas.spectrumArena", "spectrumArena"),
            Enumeration("context-state-enumeration", "Interpretation-context state enumeration",
                "FourthFifthArenas.contextArena", "contextArena"),
            Enumeration("intervention-state-enumeration", "Intervention state enumeration",
                "FourthFifthArenas.interventionArena", "interventionArena"),
            Enumeration("observation-state-enumeration",
                "Observation-intervention state enumeration",
                "ObservationIntervention.observationInterventionArena",
                "observationInterventionArena"),
            Enumeration("static-state-enumeration", "Static-experiment state enumeration",
                "StaticExactExperimentDesign.staticExactExperimentArena",
                "staticExactExperimentArena"),
            Enumeration("completion-state-enumeration", "Commuting-completion state enumeration",
                "CommutingCompletionExchange.commutingCompletionArena",
                "commutingCompletionArena"),
            Enumeration("gluing-state-enumeration", "Local-law-gluing state enumeration",
                "LocalLawGluingObstruction.localLawGluingArena", "localLawGluingArena"),
            Enumeration("preemption-state-enumeration", "Preemption-trace state enumeration",
                "EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena",
                "endStateOmitsPreemptingCauseArena"),
            Enumeration("system-state-enumeration", "SYSTEM stage enumeration",
                "SystemUnit.arena", "arena"))));

    private static readonly Formula B = F.Id("b");
    private static readonly Formula C = F.Id("C");
    private static readonly Formula E = F.Id("E");
    private static readonly Formula I = F.Id("i");
    private static readonly Formula S = F.Id("S");

    private static DocumentBlock.Describe Def(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The fold-pair classification invariant transports the list count to the " +
                    "frozen finite census."))),
            DescribeRole.Theorem);

    private static DocumentBlock.Describe Enumeration(
        string id, string title, string owner, string arena) =>
        Describe.Example(
            DescribeId.Create(id), H(title),
            Seq(F.Id("stateEnumeration"), Colon, Sp,
                Call("StateEnumeration", F.Id(arena))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                owner + ".__state_enumeration supplies an explicit duplicate-free complete " +
                    "state list."))));

    private static Formula Summary() => Call("listUniqueCaptureSummary", C, S, E, I);

    private static Formula FullCountCorrect() => Eq(
        Call("fullEscapeCount", Summary()),
        Call("escapeNumerator", C, Call("fullIndexSet", C)));

    private static Formula WithoutCountCorrect() => Eq(
        Call("withoutEscapeCount", Summary()),
        Call("escapeNumerator", C, Call("without", C, I)));

    private static Formula UniqueCountCorrect() => Eq(
        Call("uniqueCaptureCount", Summary()), Call("uniqueCaptureCount", C, I));

    private static Formula BucketCorrect() => Eq(
        Call("bucket", Summary(), B),
        Call("roleHistogram", C, I, Call("roleSignatureOfBucket", B)));

    private static Formula PositivityTransport() => Implies(
        Lt(D(0), Call("uniqueCaptureCount", Summary())),
        Lt(D(0), Call("uniqueCaptureCount", C, I)));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Eq(Formula left, Formula right) =>
        Seq(left, Sp, F.Eq, Sp, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
