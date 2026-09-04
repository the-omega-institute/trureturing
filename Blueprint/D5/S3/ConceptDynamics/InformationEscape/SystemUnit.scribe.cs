using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class SystemUnitDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/SystemUnit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Boolean coordinate CUTs give a concrete irredundant system unit.",
        H("Boolean Pair System Unit"),
        Blocks(
            Definition("bool-pair-fst-snd-signature", "boolPairFstSndSignature",
                "Boolean-pair primitive signature",
                "The signature contains two CUT slots and an empty anchor family."),
            Definition("bool-pair-fst-snd-arena", "boolPairFstSndArena",
                "Boolean-pair primitive-law arena",
                "The arena has four states and two CUT slots, with no anchor slots."),
            Definition("bool-pair-fst-snd-realization", "boolPairFstSndRealization",
                "Coordinate projection realization",
                "The two primitive readouts are the first and second Boolean projections."),
            Definition("bool-pair-fst-snd-statement", "BoolPairFstSndStatement",
                "Concrete system-unit statement",
                "The statement combines discrete joint agreement, positive empty-catalog capture, and the prescribed private pair."),
            Theorem("bool-pair-fst-snd-catalog-irredundant",
                "bool_pair_fst_snd_catalog_irredundant",
                "The coordinate system unit is irredundant", LawFormula(),
                "Finite kernel evaluation proves discrete agreement, positive capture against the empty leave-one-out family, and separation of 00 from 10."),
            Theorem("bool-pair-fst-snd-catalog-irredundant-realization",
                "bool_pair_fst_snd_catalog_irredundant_realization",
                "System-unit realization certificate", CertificateFormula(),
                "The concrete system theorem uses the same legacy-realization interface as the ten frozen applications."))));

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

    private static Formula LawFormula() => F.Id("BoolPairFstSndStatement");

    private static Formula CertificateFormula() => Call(
        "LegacyPrimitiveRealization",
        F.Id("boolPairFstSndArena"),
        F.Id("BoolPairFstSndStatement"),
        F.Id("boolPairFstSndRealization"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
