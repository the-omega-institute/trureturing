using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class AuxiliaryPolynomialFixedDegreeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-degree construction yields an auxiliary polynomial under the power inequality.",
        H("Auxiliary Polynomial Fixed Degree"),
        Blocks(Describe.Lean(
            DescribeId.Create("auxiliary-polynomial-fixed-degree"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/AuxiliaryPolynomialFixedDegree.exists_ne_zero_le_index_logHeight_le_of_pow_le"),
            H("Auxiliary Polynomial Fixed Degree"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A fixed-degree construction yields an auxiliary polynomial under the power inequality."))),
            DescribeRole.Theorem))));
}
