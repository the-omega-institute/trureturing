using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class DependencyClosedFiltrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/DependencyClosedFiltration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dependency-closed append-only filtrations order prerequisite birth no later than "
            + "dependent birth.",
        H("Dependency-Closed Filtration"),
        Blocks(Describe.Lean(
            DescribeId.Create("prerequisites-are-born-no-later"),
            DeclarationHandle.Create(Prefix + "prerequisite_birth_le"),
            H("A prerequisite is born no later than its dependent"),
            StatementSource.FromAuthor(BirthFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Quantify a dependency-filtration structure and a present dependent node. If "
                        + "a vertex is a direct prerequisite of that node, closure of every stage "
                        + "makes the prerequisite present by the dependent's birth.")),
                Paragraph(Text(
                    "The conclusion compares canonical birth times with a non-strict inequality. "
                        + "Strictly earlier birth requires the separate strict-staging hypothesis "
                        + "and is not claimed here."))),
            DescribeRole.Theorem))));

    private static Formula BirthFormula()
    {
        Formula edge = F.Id("edge");
        Formula filtration = F.Id("filtration");
        Formula dependent = F.Id("dependentNode");
        Formula prerequisite = F.Id("prerequisite");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            filtration, Colon, Sp, Call("DependencyFiltration", F.Id("V"), edge),
            Comma, RowBreak, Grp(), dependent, Colon, Sp,
            Call("PresentNode", filtration), Comma, Sp,
            prerequisite, Colon, Sp, F.Id("V"), Comma, RowBreak, Grp(),
            Call("edge", prerequisite, Call("value", dependent)), Sp, Rightarrow,
            RowBreak, Grp(),
            Call("birth", filtration,
                Call("prerequisiteNode", filtration, prerequisite, dependent)),
            Sp, Leq, Sp, Call("birth", filtration, dependent), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
