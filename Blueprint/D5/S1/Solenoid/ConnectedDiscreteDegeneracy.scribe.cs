using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class ConnectedDiscreteDegeneracyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty connected discrete topological space has exactly one point.",
        H("Connected Discrete Degeneracy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-connected-discrete-space-has-exactly-one-point"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/ConnectedDiscreteDegeneracy."
                    + "connected_discrete_has_unique_point"),
                H("A connected discrete space has exactly one point"),
                StatementSource.FromAuthor(ConnectedDiscreteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a type equipped with a topology. Assume X is nonempty and "
                            + "connected, and that its topology is discrete.")),
                    Paragraph(Text(
                        "Mathlib's PreconnectedSpace.trivial_of_discrete supplies the "
                            + "subsingleton property. ConnectedSpace supplies a point of X, so "
                            + "that point is equal to every point of X.")),
                    Paragraph(Text(
                        "Loogle and LeanSearch both identified "
                            + "PreconnectedSpace.trivial_of_discrete as the exact library result. "
                            + "Repository search found no duplicate D5 theorem."))),
                DescribeRole.Theorem))));

    private static Formula ConnectedDiscreteFormula()
    {
        Formula xType = F.Id("X");
        Formula x = F.Id("x");
        Formula y = F.Id("y");

        return Disp(Seq(
            Forall, Sp, xType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Operatorname, Grp(F.Id("TopologicalSpace")), Open, xType, Close,
            Comma, Sp,
            Operatorname, Grp(F.Id("ConnectedSpace")), Open, xType, Close,
            Comma, Sp,
            Operatorname, Grp(F.Id("DiscreteTopology")), Open, xType, Close,
            Sp, Rightarrow, Sp,
            Exists, Sp, x, Colon, Sp, xType, Comma, Sp,
            Forall, Sp, y, Colon, Sp, xType, Comma, Sp,
            y, Sp, Eq, Sp, x, Dot));
    }
}
