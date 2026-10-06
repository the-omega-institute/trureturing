using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimorialCompensatedNumeratorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PrimorialCompensatedNumerator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact initial-slope compensation gives the actual finite Euler numerator a uniform quadratic zero-end budget.",
        H("Primorial Compensated Numerator"),
        Blocks(
            Paragraph(Text(
                "For the same actual finite prime cutoff as PrimorialGlobalLaplaceEnvelope, let L=log(z), "
                + "F_z(v)=E_z(1+v/L)/E_z(1), and let S_z(v) and T_z(v) be its normalized logarithmic slope and curvature. "
                + "These suppliers stay in their original module: finite support p<=z gives 0<=T_z(v)<=2*S_z(v), "
                + "and the actual slope decreases from S_z(0). This consumer imports those public proofs.")),
            Describe.Lean(
                DescribeId.Create("actual-shifted-second-derivative"),
                DeclarationHandle.Create(Prefix + "hasDerivAt_actualShiftedRatio_derivative"),
                H("The second derivative belongs to the same actual product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Put Q_z,a(v)=exp(-a*v)*F_z(v). Its first derivative is Q_z,a(v)*(S_z(v)-a), "
                    + "and the derivative of that expression is Q_z,a(v)*((S_z(v)-a)^2-T_z(v)). "
                    + "Both identities consume the original actual ratio and slope derivatives."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-finite-cutoff-linear-cancellation"),
                DeclarationHandle.Create(Prefix + "hasDerivAt_actualCompensatedNumerator_zero"),
                H("The finite-cutoff initial slope cancels exactly"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The complete numerator is B_z,a(v)=Q_z,a(v)-1+(a-S_z(0))*v. "
                    + "For every z>=2 its derivative at zero is exactly zero. The corresponding value at zero "
                    + "is also proved zero. The finite S_z(0) is retained before any limit is taken."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-compensated-quadratic-budget"),
                DeclarationHandle.Create(Prefix + "actualCompensatedNumerator_quadratic"),
                H("The actual compensated numerator pays the zero-end singularity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write D=log(4)+4+Mertens.E1. If z>=2, D/L<=1, 0<=a<=V and 0<=v<=1, "
                        + "then abs(B_z,a(v))<=exp(2)*((V+2)^2+4)*v^2/2. "
                        + "The actual support curvature and original first-Mertens supplier bound the second derivative; "
                        + "a mean-value estimate and the fundamental theorem of calculus pay the exact factor v^2/2.")),
                    Paragraph(Text(
                        "This is a concrete zero-end supplier for the signed-kernel integral. "
                        + "The complete integral limit, fixed-cutoff tail integrability, original-profile counterpart "
                        + "and integer-fiber transport still need their own formal consumers."))),
                DescribeRole.Theorem))));
}
