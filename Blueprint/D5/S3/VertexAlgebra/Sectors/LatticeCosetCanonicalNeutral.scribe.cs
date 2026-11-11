using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetCanonicalNeutralDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticecosetcanonicalneutral-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetCanonicalNeutral", H("Full neutral action before projection"), Blocks(
            D("neutral_action_invariance", "For positive-definite original D, arbitrary external rank and integral B, every label d, every original acting state h, every original input v and integer m, Y of the neutral injection of h acts on the d injection of v as the d injection of the exact action D (B*d) h at mode m on v. The acting h may have arbitrary original charge. This holds before projection. Here the charged ground transports and arbitrary oscillator source recursion are used in mixed_integer.", DescribeRole.Theorem),
            D("compressed_neutral", "For the same complete scope, compressing the neutral source field in the d sector is exactly the existing dual-coset action with raw label B*d, on every state and mode. It identifies both ordered native Borcherds products in mixed_integer.", DescribeRole.Theorem),
            Paragraph(Text("Classical conventions: Bakalov--Kac, math/0402315v1, section 4.1. Native residue and conformal sources retain Scott Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical realization, categorical fusion completion or string completion is claimed. The original rank may be zero; all external-rank statements also include zero.")))));
}
