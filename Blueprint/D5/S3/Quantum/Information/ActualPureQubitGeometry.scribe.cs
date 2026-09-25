using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitGeometryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-two affine measurement of a pure qubit curve has a strict arc parametrization.",
        H("Pure-qubit affine geometry"),
        Blocks(
            Describe.Lean(DescribeId.Create("spectral-sld-information"),
                DeclarationHandle.Create(Module + "spectralQFI"), H("Spectral SLD information"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In an eigenbasis of the positive semidefinite state, sum twice the squared "
                    + "modulus of each derivative entry divided by the sum of the corresponding "
                    + "eigenvalues. Terms with zero denominator are zero. Positivity on a "
                    + "two-sided neighborhood forces the derivative's kernel-to-kernel block to vanish "
                    + "(Pker D Pker = 0)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("guarded-real-infimum"),
                DeclarationHandle.Create(Module + "guardedInfimum"), H("Guarded real infimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Real infimum with explicit nonempty and bounded-below guard."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("canonical-density-bridge"),
                DeclarationHandle.Create(Module + "densityBridge"), H("Canonical density-state bridge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every positive semidefinite trace-one matrix is constructed as a canonical "
                    + "density state, with exact equality of the recovered matrix."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-program-class"),
                DeclarationHandle.Create(Module + "IsProgram"), H("Full actual program class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A fixed finite POVM and a continuously differentiable pure state curve are "
                    + "defined on an open connected interval containing the closed radius interval. "
                    + "Born probabilities are exactly affine and positive throughout. The cost is "
                    + "the actual spectral SLD information at zero. No readout rank, score sign, "
                    + "canonical arc, or zero-score effect shape is imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cost-set"),
                DeclarationHandle.Create(Module + "costs"), H("Attainable actual costs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The set ranges over all actual programs in the preceding class."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cost-infimum"),
                DeclarationHandle.Create(Module + "C2"), H("Cost infimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real infimum is used only in the branch with nonempty and lower-bounded "
                    + "cost set. Both conditions hold at every sufficiently small positive radius."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bloch"),
                DeclarationHandle.Create(Module + "bloch"), H("Bloch vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three real Bloch coordinates of a two by two matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochmatrix"),
                DeclarationHandle.Create(Module + "blochMatrix"), H("Bloch matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Hermitian matrix with a specified real trace and Bloch vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effectreadout"),
                DeclarationHandle.Create(Module + "effectReadout"), H("Visible readout map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linear part of the finite measurement readout sends a Bloch vector to its pairings with the effect vectors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reframe"),
                DeclarationHandle.Create(Module + "reframe"), H("Orthogonal change of Bloch coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An orthogonal change of the Bloch vector preserves the trace coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochlinear"),
                DeclarationHandle.Create(Module + "blochLinear"), H("Linear Bloch map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch coordinates form a real linear map on complex matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reframelinear"),
                DeclarationHandle.Create(Module + "reframeLinear"), H("Linear change of matrix coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed orthogonal Bloch frame induces a real linear map on matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("root"),
                DeclarationHandle.Create(Module + "root"), H("Small quadratic root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rationalized small root gives the lower diagonal effect coefficient, including zero individual scores."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radiusmap"),
                DeclarationHandle.Create(Module + "radiusMap"), H("Radius map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The radius includes a strict margin inside the pure-state arc and is locally inverted near zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extendedcost"),
                DeclarationHandle.Create(Module + "extendedCost"), H("Extended family cost"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cost formula extends through the zero transverse parameter for the normalization branch."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upperdiag"),
                DeclarationHandle.Create(Module + "upperDiag"), H("Upper diagonal coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complementary quadratic root determines the upper diagonal effect coefficient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effect"),
                DeclarationHandle.Create(Module + "effect"), H("Actual effect matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two diagonal coefficients and the normalized direction determine each effect matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arc"),
                DeclarationHandle.Create(Module + "arc"), H("Pure-state arc"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch curve has one affine coordinate, one square-root coordinate, and one constant coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-rank-two-parameters"),
                DeclarationHandle.Create(Module + "actual_rank_two_parameters"), H("Actual rank-two arc and feasible coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual rank-two affine readout of a pure curve admits a fixed orthonormal frame. The invisible coordinate has constant sign on the connected open interval. The effect coefficients satisfy positivity, normalization, and the exact affine-readout relations; the visible coordinate satisfies the strict radius bound.")))))));
}
