using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Conservation;

internal sealed class ExpansionTowerFullMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Atomless probability naming systems and their expansion limits remain anonymous almost everywhere.",
        H("Anonymous Full Measure Along Expansion Towers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("naming-expansion-full-measure"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/Conservation/ExpansionTowerFullMeasure."
                    + "naming_expansion_full_measure"),
                H("Naming expansions preserve full-measure anonymity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("X"), Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("MeasureSpace")),
                    Open, F.Id("X"), Close, CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Uncountable")),
                    Open, F.Id("X"), Close, CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("NoAtoms")),
                    Open, Mu, Close, CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("IsProbabilityMeasure")),
                    Open, Mu, Close, CloseBracket, Comma, RowBreak,
                    Open, Forall, Sp, F.Id("N"), Colon, Sp,
                    Operatorname, Grp(F.Id("NamingSystem")), Open, F.Id("X"), Close, Comma, Esc,
                    Mu, Open, Operatorname, Grp(F.Id("anonymous")),
                    Open, F.Id("N"), Close, Close, Eq, D(1), Close,
                    Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("T"), Colon, Sp,
                    Operatorname, Grp(F.Id("ExpansionTower")), Open, F.Id("X"), Close, Comma, Esc,
                    Mu, Open, Operatorname, Grp(F.Id("limitAnonymous")),
                    Open, F.Id("T"), Close, Close, Eq, D(1), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A naming system's anonymous set is the complement of the image of its "
                            + "partial assignment. An expansion tower consists of successor "
                            + "embeddings of name types whose assignments agree with the previous "
                            + "stage; its limit named set is the union over all finite stages.")),
                    Paragraph(Text(
                        "The first conjunct quantifies over every naming system independently. "
                            + "The second quantifies over every compatible countable expansion "
                            + "tower. Thus both clauses of the named source statement are retained, "
                            + "including probability normalization and the limit-system carrier.")),
                    Paragraph(Text(
                        "The proof applies the frozen countable-tower full-measure theorem twice: "
                            + "first to the singleton-indexed family and then to the stages of the "
                            + "tower. Pinned Mathlib's probability-measure identity changes the "
                            + "measure of the whole carrier to one."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Naming/Conservation/NamingTowerConservation"))]));
}
