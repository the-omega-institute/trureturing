using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;
internal sealed class SixRowMaximumPurityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-row actual APPT maximum and least eventual central threshold", H("SixRowMaximumPurity"), Blocks(
            Describe.Lean(DescribeId.Create("sixrowmaximum-centraloptimal"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.CentralOptimal"),
                H("CentralOptimal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual complex matrix rho on Fin 6 times Fin n, PSD, complex trace one and literal all-global-unitary APPT imply real trace-square purity at most the existing SixRowScalarData.theta(n). There also exists an actual rho with all these properties and purity equal to theta(n). Ordered-spectrum uniqueness is not part of this predicate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowmaximum-eventualcentralfrom"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.EventualCentralFrom"),
                H("EventualCentralFrom"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, 6<=n and k<=n imply CentralOptimal(n). The threshold concerns universal actual-density maximality together with actual attainment."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowmaximum-central-optimal"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.central_optimal"),
                H("central optimal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n>=23, SixRowLiteralUpper.density_upper supplies the universal bound for arbitrary complex PSD trace-one APPT rho. SixRowAttainment.central_attainment supplies an actual equality witness centralDensity(n): its second conjunction projection drops only the projector-rank clause and retains PSD, trace one, APPT and exact purity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowmaximum-ordered-spectrum-upper-and-equality"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.ordered_spectrum_upper_and_equality"),
                H("ordered spectrum upper and equality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Independently, for every n>=23, every product-to-Fin equivalence e and arbitrary original antitone nonnegative unit-mass spectrum l whose actual e-labelled complex diagonal is APPT, the square sum is at most theta(n), and equals theta(n) iff l is exactly SixRowConcentration.centralSpectrum(n). This consumes SixRowLiteralUpper.literal_upper_and_equality. Repeated and zero entries are allowed; no concentrated vector is assumed APPT and no unique-matrix claim is made."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowmaximum-central-spectrum-attainment"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.central_spectrum_attainment"),
                H("central spectrum attainment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n>=23, the named centralSpectrum(n) is antitone, nonnegative, has mass one and square sum theta(n). Its actual diagonal under finProdFinEquiv is PSD, trace one, literal APPT and has purity theta(n). Unfolding only centralSpectrum matches SixRowAttainment.central_spectrum_data and central_density_diagonal; central_attainment supplies the physical properties. The first j=(5*n+1)/2 entries are 7/(30*n+2*j), and all remaining entries are 5/(30*n+2*j)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowmaximum-eventual-central-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.eventual_central_iff"),
                H("eventual central iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural k, EventualCentralFrom(k) iff 23<=k. Sufficiency uses central_optimal for each n>=k. If k<=22, instantiate the purported universal result at n=22 and apply its actual-density upper clause to SixRowAttainment.ray22Density. The physical n22_obstruction supplies PSD, trace one, APPT and strict purity greater than theta(22), contradicting that clause. Its exact values are 35/4489 and theta(22)=3/385, differing by 8/1728265; uniqueness is not used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowmaximum-eventual-threshold-is-least"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.eventual_threshold_is_least"),
                H("eventual threshold is least"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural number 23 is IsLeast of the set of k with EventualCentralFrom(k), directly from eventual_central_iff."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowmaximum-n0"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.n0"),
                H("n0"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nat.find of the established nonempty predicate EventualCentralFrom defines the least eventual central-maximum threshold. The existence witness is 23; the definition does not impose ordered-spectrum uniqueness."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowmaximum-n0-eq"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.n0_eq"),
                H("n0 eq"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defined n0 equals 23. Nat.find_min' gives n0<=23, and Nat.find_spec with eventual_central_iff gives 23<=n0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowmaximum-result"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.result"),
                H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The final theorem combines actual universal maximum and actual attainment for every n>=23, independent arbitrary original ordered-spectrum equality, the existing exact parity formula theta(n)=6/(35*n) for even n and 6*(35*n+2)/(35*n+1)^2 for odd n, IsLeast of the eventual central-maximum thresholds at 23, and n0=23. It adds no target-equivalent assumption and does not determine maxima for 6<=n<=22. Tran, arXiv:2611.01492v1, Theorem A and the final discussion, gives the prior n>=68 range and asks for the least fixed-row threshold."))), DescribeRole.Theorem)
        )));
}
