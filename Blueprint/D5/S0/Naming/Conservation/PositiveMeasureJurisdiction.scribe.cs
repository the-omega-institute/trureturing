using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Conservation;

internal sealed class PositiveMeasureJurisdictionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-measure naming jurisdictions contain uncountably many source points.",
        H("Positive-Measure Naming Jurisdictions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-measure-jurisdiction-uncountable"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/Conservation/PositiveMeasureJurisdiction."
                    + "positive_measure_jurisdiction_uncountable"),
                H("Positive-measure jurisdictions are uncountable"),
                StatementSource.FromAuthor(PositiveJurisdictionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let system be a naming system on a measured source X, let encode map "
                            + "source points to its names, and let name be one such name. The "
                            + "jurisdiction of name is the fiber of encode over name.")),
                    Paragraph(Text(
                        "If the source measure is atomless and that jurisdiction has positive "
                            + "measure, then the jurisdiction is not countable.")),
                    Paragraph(Text(
                        "The proof applies Mathlib's Set.Countable.measure_zero directly: a "
                            + "countable jurisdiction would have zero measure, contradicting "
                            + "the positive-measure hypothesis."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Naming/NamingSystem"))]));

    private static Formula PositiveJurisdictionFormula()
    {
        Formula system = F.Id("system");
        Formula encode = F.Id("encode");
        Formula name = F.Id("name");
        Formula jurisdiction = Seq(
            F.Id("fiber"), Open, encode, Comma, Sp, name, Close);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("X"), Comma, Sp, system, Comma, Sp, encode, Comma, Sp, name,
            Comma, RowBreak,
            system, Colon, Sp, F.Id("NamingSystem"), Open, F.Id("X"), Close, Comma, Sp,
            encode, Colon, Sp, F.Id("X"), To, Sp,
            F.Id("Name"), Open, system, Close, Comma, Sp,
            name, Colon, Sp, F.Id("Name"), Open, system, Close, Comma, RowBreak,
            F.Id("NoAtoms"), Open, Mu, Close, Sp, Land, Sp,
            D(0), Lt, Sp, Mu, Open, jurisdiction, Close, Sp,
            Rightarrow, Sp, Neg, Sp, F.Id("Countable"), Open, jurisdiction, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
