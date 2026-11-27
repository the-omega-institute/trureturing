using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaNormality;

internal sealed class NormalGenerationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal Generation", H("Normal Generation"),
        Blocks(
            Paragraph(Text("Every point is centre of a rank-one valuation at a dense complex point. Finite products of proper schemes over a base are proper. Sup-norm balls of theta functions: powers of balls are balls, rank of reduction.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/NormalGeneration.thetaNorm_lt_iff_coords"),
                H("thetaNorm_lt_iff_coords"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Assume HasGoodReduction. Let (x_j) enumerate the ball of a theta function f ≠ 0, (a_b) meet every class of L^∨/L, and p_b primitively scale (x_j(a_b))_j. Then ‖x_j‖ < ‖f‖ iff p_{b,j} is a non-unit for all b.")))))));
}
