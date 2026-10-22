using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalSignedPrimeBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/OriginalSignedPrimeBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original_prime80 estimate applies to c=5040 or c=5041, every M beyond the inclusive cutoff, and arbitrary complex WindowL2 input on the original Ioc window.",
        H("OriginalSignedPrimeBound"),
        Blocks(
                Paragraph(Text("The original_prime80 estimate applies to c=5040 or c=5041, every M beyond the inclusive cutoff, and arbitrary complex WindowL2 input on the original Ioc window.")),
                Paragraph(Text("The estimate uses all 717 prime-power rows and 141 closed cells. The arithmetic certificate checks row facts and rational log ceilings directly. A strictly increasing adjacent chain implies nodup. Equality with the prime-factor-cardinality-one filter of the complete range 5041 proves every Fin 5041 support equivalence. The geometry proof constructs CellCertificate by two direct scripts: all recomputed cell inequalities and the exact nonempty chain.")),
                Paragraph(Text("For each of the two c values, log(c)/2<=log(71) follows from log monotonicity and 5041=71^2. The existing floor(exp(2*a)) cutoff equals c, and primeAction_cutoff handles every larger M. original_prime_integral identifies the negative primeSymmetric integral with negative primeQuadratic. The parameterized MemLp bound and existing l2_energy then produce the exact norm-square target.")),
                Paragraph(Text("At 5041, the original primeWeight is log(71)/71 and is positive. It is not set to zero by the table or proof. The existing touching-endpoint Ioc compression identities kill the translated contribution. Both shifts, the negative symmetric action, dx normalization, and the full complex domain remain.")),
                Describe.Lean(DescribeId.Create("original-prime80"),
                    DeclarationHandle.Create(Owner + "original_prime80"), H("original prime80"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The original complex L2 estimate combines the variable-certificate inference and all six exact arithmetic and cell checks."))), DescribeRole.Theorem))));
}
