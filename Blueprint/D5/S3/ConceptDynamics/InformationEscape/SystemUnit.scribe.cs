using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class SystemUnitDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/SystemUnit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The escape engine characterizes its own census on a two-stage arena.",
        H("Engine Census Self-Application"),
        Blocks(
            Definition("stage", "Stage", "Stage type",
                "The finite meta-arena has a before and an after stage."),
            Definition("census-arena", "censusArena", "Census arena",
                "The engine census ranges over the two Boolean states."),
            Definition("census-catalog", "censusCatalog", "Stage-indexed catalog",
                "Its lone CUT is constant before separation and identity afterward."),
            Definition("system-readout", "systemReadout", "SYSTEM readout",
                "The readout is the canonical leave-one-out unique-capture count."),
            Definition("system-characterization", "SystemCharacterization",
                "Engine characterization",
                "Every stage specializes the canonical exact-rate criterion."),
            Definition("arena", "arena", "Primitive-law Stage arena",
                "One CUT slot reads a natural-valued engine census at each stage."),
            Definition("system-realization", "systemRealization",
                "Census realization",
                "The realization calls the catalog's unique-capture census directly."),
            Definition("system-statement", "SystemStatement", "SYSTEM statement",
                "The law joins readout identity, exact-rate characterization, and " +
                "true-stage irredundancy."),
            Theorem("engine-census-self-application", "engine_census_self_application",
                "The engine census self-applies", SelfApplicationFormula(),
                "The canonical exact-rate theorem proves the characterization; " +
                "the stage census changes from zero to two."),
            Theorem("system-self-application-realization",
                "system_self_application_realization",
                "Self-application realization certificate", CertificateFormula(),
                "The SYSTEM theorem uses the same legacy registration interface as " +
                "the ten frozen applications."))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string title, Formula formula, string explanation) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);

    private static Formula SelfApplicationFormula()
    {
        Formula stage = F.Id("stage");
        Formula catalog = Call("censusCatalog", stage);
        Formula count = Call("uniqueCaptureCount", catalog, D(0));
        Formula readout = Call("readout", F.Id("systemRealization"), D(0), stage);
        Formula characterization = Seq(
            Forall, Sp, stage, Colon, Sp, F.Id("Stage"), Comma, RowBreak,
            Call("LowersEscape", catalog, D(0)), Sp, Iff, Sp,
            D(0), Sp, Lt, Sp, count);
        return Seq(
            Open, Forall, Sp, stage, Colon, Sp, F.Id("Stage"), Comma, RowBreak,
            readout, Sp, Eq, Sp, count, Close, Sp, Land, RowBreak,
            Open, characterization, Close, Sp, Land, RowBreak,
            Call("CatalogIrredundant", Call("censusCatalog", F.Id("true"))));
    }

    private static Formula CertificateFormula() => Call(
        "LegacyPrimitiveRealization",
        F.Id("arena"),
        F.Id("SystemStatement"),
        F.Id("systemRealization"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
