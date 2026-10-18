using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CfmResolventInterpolationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CfmResolventInterpolation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three spectral nodes control the two mixed resolvent products with constant 54.",
        H("A three-node resolvent estimate"),
        Blocks(Describe.Lean(
            DescribeId.Create("cfm-mixed-resolvent-control"),
            DeclarationHandle.Create(Module + ".mixed_resolvent_control"),
            H("Uniform control of mixed resolvents"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let C be a complex Hermitian 3 by 3 matrix with every eigenvalue below one, "
                    + "and put R_s=(sI−C)⁻¹. For any real linear observation L into a real seminormed space, "
                    + "the sum of the squared norms of L(R_2 R_4) and L(R_3 R_4) is at most "
                    + "54 times the sum of the squared norms of L(R_2²), L(R_2 R_3), and L(R_3²).")),
                Paragraph(Text("Write y_i=3−λ_i>2 and d=∏(y_i+1). At each of the three spectral nodes, "
                    + "interpolation gives R_2 R_4=c_1 R_2²+c_2 R_2 R_3+c_3 R_3², where "
                    + "c_1=∏(y_i−1)/d, c_2=2(e_2−e_3)/d, and c_3=2e_3/d. The second mixed product "
                    + "has coefficients 2c_1, 2c_2−1, 2c_3. Their squared coefficient sums are bounded "
                    + "by 9 and 45. The continuous functional calculus lifts the spectral identities; "
                    + "a three-term Cauchy–Schwarz estimate gives 9+45=54. Distinct eigenvalues are not required."))),
            DescribeRole.Theorem))));
}
