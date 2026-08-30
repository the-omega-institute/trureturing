using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class BooleanFlipNoFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/BooleanFlipNoFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical exchange of the two Boolean statuses has no fixed point.",
        H("Boolean Flip Has No Fixed Point"),
        Blocks(Describe.Lean(
            DescribeId.Create("boolean-flip-has-no-fixed-point"),
            DeclarationHandle.Create(Prefix + "bool_flip_has_no_fixed_point"),
            H("Boolean flip has no fixed point"),
            StatementSource.FromAuthor(NoFixedPointFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The Boolean carrier has exactly the statuses false and true, and boolFlip "
                        + "exchanges them.")),
                Paragraph(Text(
                    "Constructor analysis therefore contradicts either proposed fixed-point "
                        + "equation without asserting anything about arbitrary non-blind "
                        + "derivers."))),
            DescribeRole.Theorem))));

    private static Formula NoFixedPointFormula()
    {
        Formula status = F.Id("status");

        return Disp(Seq(
            Neg, Sp, Exists, Sp, status, Colon, Sp, F.Id("Bool"), Comma, Sp,
            status, Sp, Eq, Sp,
            F.Id("boolFlip"), Open, status, Close, Dot));
    }
}
