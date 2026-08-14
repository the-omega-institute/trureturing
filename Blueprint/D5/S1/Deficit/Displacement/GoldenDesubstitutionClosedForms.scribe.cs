using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Displacement;

internal sealed class GoldenDesubstitutionClosedFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two face lengths have individual closed forms in terms of the hidden product nS.",
        H("Golden Desubstitution Face-Length Closed Forms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-expansion-face-closed-form"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms.lambdaPlus_eq_log_nS_sub_goldenConj_log"),
                H("The expansion-face length has a hidden-product closed form"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("n"), Neq, D(0), Sp, Implies, Sp,
                    LambdaLower, Underscore, Grp(Plus), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    Log, Open, F.Id("nS"), Sp, F.Id("n"), Close, Sp, Minus, Sp,
                    Psi, Sp, Cdot, Sp, Log, Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Expanding log n and log(nS n) over their prime factorizations reduces the equality "
                        + "to one identity for each exponent. The hidden product replaces an exponent by "
                        + "its golden substitution start, which is the Zeckendorf displacement decode. "
                        + "The expansion-face beta reading is exactly that displacement minus the original "
                        + "exponent multiplied by the golden conjugate, so the finite sums agree termwise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-contraction-face-closed-form"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms.lambdaMinus_eq_log_nS_sub_goldenRatio_log"),
                H("The contraction-face length has a hidden-product closed form"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("n"), Neq, D(0), Sp, Implies, Sp,
                    LambdaLower, Underscore, Grp(Minus), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    Log, Open, F.Id("nS"), Sp, F.Id("n"), Close, Sp, Minus, Sp,
                    Phi, Sp, Cdot, Sp, Log, Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same factorization expansion applies on the contraction face. The public two-face "
                        + "spread and the identity phi minus psi equals sqrt(5) convert the expansion reading "
                        + "into the conjugate reading: displacementDecode at an exponent minus phi times that "
                        + "exponent. Summing these exponentwise identities gives log(nS n) minus phi log n."))),
                DescribeRole.Theorem))));
}
