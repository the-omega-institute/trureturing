using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class ThreeAtomZeroFilterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive filters for prescribed conjugate modes",
        H("Positive filters for prescribed conjugate modes"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-three-atom-zero-filter"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter.exists_threeAtom_zero_filter"),
            H("A positive measure can annihilate a conjugate pair and preserve a distinct mode"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Choose three positive masses at 0, a and 2a. The exponential transform factors into "
                + "two linear factors in the exponential variable. Avoid the countable set of spacings "
                + "where either factor would vanish at the protected mode."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("exists-selective-spectral-filter"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter.exists_selective_spectral_filter"),
            H("A compact probability for summably sparse selected modes"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Use the three-atom factors at the selected indices and point masses at zero at the "
                + "other indices. Summability of the reciprocal positive ordinates bounds the total "
                + "support length. The product vanishes at each selected conjugate pair and remains "
                + "nonzero at the protected mode."))),
            DescribeRole.Theorem))));
}
