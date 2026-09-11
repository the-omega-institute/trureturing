using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class FlatProjectorDephasingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical dephasing of flat rank-one projections for exhaustive root-cover consumers.",
        H("Flat Projector Dephasing"),
        Blocks(Describe.Lean(
            DescribeId.Create("flat-projector-canonical-dephased-root"),
            DeclarationHandle.Create("D5/S3/Quantum/Tomography/FlatProjectorDephasing.flat_rankOne_projector_has_canonical_dephased_root"),
            H("Recover a dephased common-unbiased root from an actual projector"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("CanonicalFlatProjectorRoot"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For an existing IsNormalizedRankOneProjection P in dimension six with diagonal one-sixth, define u_i=6P_i0. The theorem proves u_0=1, every u_i has squared modulus one, reconstructs P_ij=u_i conjugate(u_j)/6, and translates the second-basis diagonal condition into squared modulus six for H-adjoint u. The proof reuses the existing rank-one compression law and introduces no second projector or basis carrier. Root isolation and interval-cover soundness remain separate obligations."))),
            DescribeRole.Theorem))));
}
