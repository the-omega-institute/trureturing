using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMAmplitudeCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMAmplitudeCertificates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform amplitude bound from the complete original EJM triangle coefficient tree.",
        H("Exact original coefficient amplitudes for physical noise estimates"),
        Blocks(
            Paragraph(Text("The private numerical receipt kernel-checks the recursive amplitude checker on the existing complete triangle coefficient tree. The proof traverses the original stored coefficients and imports the original F1 definition; it neither duplicates the data nor enumerates all four-valued outcome assignments. Generic tree-interpreter soundness then applies at each actual local symmetry orbit key. Casting this integer bound to the reals supplies the amplitude premise used by EJMNoiseRegion.actual_noise_box. The checker, actual numerical premise and substantive noise consumer belong to one delivery after the actual global positivity premise is earned. Amplitude alone gives no positive inflation-score margin or nonlocality conclusion.")),
            Describe.Lean(DescribeId.Create("f1-integer-amplitude"),
                DeclarationHandle.Create(Prefix + "actual_F1_abs_bound"),
                H("Original F1 integer amplitude"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every ten-coordinate event, the absolute value of the original triangle coefficient F1 is at most 53480245575024. The premise checking this bound on the entire original tree is discharged by a kernel computation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("f1-real-amplitude"),
                DeclarationHandle.Create(Prefix + "actual_F1_real_abs_bound"),
                H("Original F1 real amplitude for noise estimates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact integer F1 amplitude is transported to the real cast of the same original coefficient function. It supplies the 53480245575024 amplitude input of the physical noise-box theorem; a positive score margin remains a separate obligation."))),
                DescribeRole.Theorem))));
}
