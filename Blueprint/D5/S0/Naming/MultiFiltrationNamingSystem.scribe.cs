using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class MultiFiltrationNamingSystemDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A primary naming filtration remains finite after a secondary budget is imposed.",
        H("Multi-Filtration Naming System"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-budget-layer-is-finite"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/MultiFiltrationNamingSystem."
                        + "joint_budget_layer_finite"),
                H("Joint budget layers remain finite"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The structure wraps the canonical NamingSystem as its primary field and "
                            + "adds one secondary height on exactly the same name carrier.")),
                    Paragraph(Text(
                        "Every joint budget layer is a subset of the corresponding primary layer. "
                            + "Its finiteness therefore uses only the primary owner's finite-layer "
                            + "law and imposes no filtration law on the secondary height."))),
                DescribeRole.Lemma)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Naming/NamingSystem"))]));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("X");
        Formula system = F.Id("M");
        Formula primaryBudget = F.Id("QK");
        Formula secondaryBudget = F.Id("QC");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrier, Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("MeasureSpace", carrier), CloseBracket, Comma, RowBreak, Grp(),
            Forall, Sp, system, Colon, Sp,
            Call("MultiFiltrationNamingSystem", carrier), Comma, RowBreak, Grp(),
            Forall, Sp, primaryBudget, Comma, Sp, secondaryBudget,
            Colon, Sp, naturals, Comma, RowBreak, Grp(),
            Call("Finite", Call("jointLayer", system, primaryBudget, secondaryBudget)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
