using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class FiniteQuotientResidualHierarchyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientResidualHierarchy."
        + "finite_quotient_residual_hierarchy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite nilpotent quotient observations lie inside the finite solvable quotient "
            + "observations, which lie inside all finite quotient observations; their kernel "
            + "residuals are ordered in reverse.",
        H("Finite Quotient Languages and Their Residual Hierarchy"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-quotient-language-residual-hierarchy"),
            DeclarationHandle.Create(Declaration),
            H("Larger quotient languages have smaller common kernels"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A quotient channel is represented canonically by a normal subgroup and "
                        + "its quotient map. The finite, finite solvable, and finite nilpotent "
                        + "languages select channels by properties of those quotient targets.")),
                Paragraph(Text(
                    "Every nilpotent group is solvable, while finiteness is explicitly retained "
                        + "when a nilpotent channel is viewed as solvable and when a solvable "
                        + "channel is viewed as finite. These facts give the first two displayed "
                        + "language inclusions on the same normal-quotient carrier.")),
                Paragraph(Text(
                    "The finite residual is the frozen object from the adjacent finite-quotient "
                        + "faithfulness theorem. The other residuals intersect the kernels over "
                        + "the selected solvable and nilpotent languages. An intersection over "
                        + "more channels is smaller, giving both displayed reverse inclusions. "
                        + "This closes atom generic-residual-1af9114aad5514c525c71e338c1ccb4f"
                        + "142b4afe6fedc0d198daa73a4e456caa."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula finiteLanguage = Call("finiteQuotientLanguage", group);
        Formula solvableLanguage = Call("solvableQuotientLanguage", group);
        Formula nilpotentLanguage = Call("nilpotentQuotientLanguage", group);
        Formula finiteKernel = Call("finiteResidual", group);
        Formula solvableKernel = Call("solvableResidual", group);
        Formula nilpotentKernel = Call("nilpotentResidual", group);

        return Disp(Seq(
            Forall, Sp, group, Comma, Sp, Call("Group", group), Sp, Rightarrow, RowBreak, Grp(),
            Open, nilpotentLanguage, Sp, Subseteq, Sp, solvableLanguage, Close,
            Sp, Land, RowBreak, Grp(),
            Open, solvableLanguage, Sp, Subseteq, Sp, finiteLanguage, Close,
            Sp, Land, RowBreak, Grp(),
            Open, finiteKernel, Sp, Subseteq, Sp, solvableKernel, Close,
            Sp, Land, RowBreak, Grp(),
            Open, solvableKernel, Sp, Subseteq, Sp, nilpotentKernel, Close, Dot));
    }
}
