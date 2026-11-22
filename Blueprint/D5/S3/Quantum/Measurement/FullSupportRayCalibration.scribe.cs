using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FullSupportRayCalibrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A calibration on a basis and a single full-support input determines a branch coefficient map up to one scalar relative to an injective reference.",
        H("Support-sensitive calibration of a branch coefficient map"),
        Blocks(Describe.Lean(DescribeId.Create("support-calibration"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/FullSupportRayCalibration.support_calibration"),
            H("Which diagonal coefficients an additional input identifies"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("T"), Open, F.Id("u"), Close, Sp, Eq, Sp, F.Id("c"),
                F.Id("J"), Open, F.Id("u"), Close, Sp, Iff, Sp, Forall, Sp, F.Id("i"), Sp, InMacro, Sp,
                F.Id("supp"), Open, F.Id("u"), Close, Comma, Sp, new Formula.Subscript(F.Id("a"), F.Id("i")),
                Sp, Eq, Sp, F.Id("c")))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let J be an injective linear reference map between vector spaces over a field. For a finite input basis, suppose T sends each basis vector to a scalar aᵢ times its J-image. The extra test T(u)=cJ(u) holds exactly when aᵢ=c at every nonzero coordinate of u. If all coordinates of u are nonzero, passing the test is equivalent to T=cJ on the whole input.")),
                Paragraph(Text("Expand u in the basis, push both linear maps through the finite sum, and cancel the injective J. The resulting coordinate equations are uᵢaᵢ=uᵢc. For a quantum instrument, J can be the inclusion of an outcome subspace and T the restriction of a Kraus operator. Applying the criterion to each such coefficient requires that the measured pure-state calibrations have first been converted to the stated ray-preservation hypotheses."))), DescribeRole.Theorem))));
}
