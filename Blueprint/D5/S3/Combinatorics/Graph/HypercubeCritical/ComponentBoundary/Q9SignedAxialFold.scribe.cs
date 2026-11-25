using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SignedAxialFoldDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity-gauged signed axial fold",
        H("Parity-gauged signed axial fold"),
        Blocks(
            Paragraph(Text("The intended application of the signed Huang equations is the " +
                "normalized order-ninety cylinder for Hong–Wu–Xia, arXiv:2610.09483 §7, Problem " +
                "2. The fold works for any coherently switched induced cubic support of the " +
                "nine-cube, with the first coordinate taken as the axis.")),
            Describe.Lean(
                DescribeId.Create("projected-parity-sign"),
                DeclarationHandle.Create(Module + ".paritySign"),
                H("Projected parity sign"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write P(x) for the sign of the parity of the eight " +
                    "retained bits. It is +1 on even sites and −1 on odd sites. Its square is " +
                    "one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("projected-parity-flip"),
                DeclarationHandle.Create(Module + ".paritySign_flip"),
                H("A transverse flip reverses projected parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Flipping one retained bit reverses P. The fold uses this " +
                    "identity to gauge the transverse row. " +
                    "Q9ConnectorResidual.residual_at_connector uses it to pass from the odd " +
                    "connector to an even neighbour and then to an odd residual site."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-transverse-row"),
                DeclarationHandle.Create(Module + ".transverse"),
                H("Signed transverse row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native eight-cube Huang row H sums the values at the " +
                    "eight transverse flips with their signed edge coefficients. Since each " +
                    "flip reverses P, the row of the pointwise product P·v is −P times the row " +
                    "of v."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-switching-word"),
                DeclarationHandle.Create(Module + ".signedWord"),
                H("Integer switching word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a selected vertex x, the integer word is +1 if s(x) = " +
                    "1 and −1 otherwise. It is zero off the support. For a coherent switching, " +
                    "its real cast is the zero-extended switching vector. The ambient " +
                    "degree-three eigenvector relation therefore gives the signed nine-cube row " +
                    "equation over the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parity-gauged-layer"),
                DeclarationHandle.Create(Module + ".gaugeLayer"),
                H("Parity gauge of the axial layers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An axial layer fixes the first bit. The gauge takes the " +
                    "true layer directly and multiplies the false layer by P. The original " +
                    "axial coupling has coefficient one and the transverse terms have opposite " +
                    "signs in the two layers. After the gauge, both transverse operators are H " +
                    "and the coupling is multiplication by P."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-fold-equations"),
                DeclarationHandle.Create(Module + ".signed_fold"),
                H("Complementary equations for the folded modes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a and b be the gauged true and false layers. The two " +
                        "row equations are Ha + P·b = 3a and Hb + P·a = 3b. Adding and " +
                        "subtracting gives Hg = (3 − P)g for the sum g = a + b and Hh = (3 + " +
                        "P)h for the difference h = a − b. Each folded mode combines both axial " +
                        "layers.")),
                    Paragraph(Text("In the majority-even normalization of the order-ninety " +
                        "case, the sum row is 2g at an even projected site and 4g at an odd " +
                        "site. The difference has the complementary coefficients. Thus an " +
                        "actual even singleton has sum value ±1 and contributes a nonzero row " +
                        "of the sum mode."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/" +
                "Q9OccupiedFibreParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance"))
        ]));
}
