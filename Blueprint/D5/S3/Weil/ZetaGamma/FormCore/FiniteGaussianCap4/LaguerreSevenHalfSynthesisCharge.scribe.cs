using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class LaguerreSevenHalfSynthesisChargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual synthesis and central Mellin charge",
        H("Actual synthesis and central Mellin charge"),
        Blocks(
            Paragraph(Text("The second physical coordinate of the weighted Laguerre synthesis belongs to L1 on x>0 with measure x^(5/4) dx. Its Bochner integral is a continuous linear functional J. This is the central Mellin charge used by the actual Gaussian coefficient core; it is not an identification with the original H6 full-line constraint.")),
            Describe.Lean(
                DescribeId.Create("laguerre-seven-half-synthesis-charge"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfSynthesisCharge.synthesis_mellin_charge"),
                H("Physical integration equals actual coefficient charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every weighted square-summable coefficient vector w, J(synthesis(w)) equals m0 times the continuous actual coefficient charge, where m0 is the positive zeroth normalized central Mellin integral. Each finite single mode is integrated against the literal measure, and continuity transports the convergent synthesis series. The actual ell2 inner-product series has the same terms; uniqueness of their sums proves the identity. No termwise integral interchange, Laguerre completeness, closed image or original-domain surjectivity is assumed. The inherited Laguerre polynomial source retains its upstream OpenAI/math attribution and Apache-2.0 notice. This source-relative result makes no RH-resolution or literature-priority claim."))),
                DescribeRole.Theorem))));
}
