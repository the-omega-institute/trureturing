using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.JainAbsCosine;

internal sealed class SeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict separation of nonzero absolute cosine Fourier modes.",
        H("Separation of Fourier representatives"), Blocks(
            Describe.Lean(DescribeId.Create("jain-mode-below-top"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/Separation.modeValue_lt_top"),
                H("Strictly largest constant mode"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive natural m, every natural j between one and m, and every real exponent r, mode j is strictly smaller than mode zero. Each difference summand is nonnegative. The first is strictly positive because its cosine phase lies strictly between zero and pi and its power base is positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-nonzero-mode-injectivity"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/Separation.modeValue_injective_nonzero"),
                H("Distinct representatives of nonzero modes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real exponent r, representatives with indices between one and m that agree at a nonzero value have equal indices. The exact mode and gap signs reduce the comparison to the root products P(j)=product of r-2s for s less than j. Between two indices with equal nonzero sign, one can advance by one index when r exceeds twice the current index, and by two indices otherwise. Equality at that threshold would force the target root product to vanish. The signs of the corresponding gaps give strict ordering along the resulting finite chain. This argument applies to negative exponents as well as to the nonnegative range of the multiplicity claim."))), DescribeRole.Theorem))));
}
