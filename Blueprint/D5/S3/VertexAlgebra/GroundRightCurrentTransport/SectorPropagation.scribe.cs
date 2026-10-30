using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class SectorPropagationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GroundRightCurrentTransport/SectorPropagation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SectorPropagation",
        H("SectorPropagation"),
        Blocks(
            Paragraph(Text("SectorGroundPair quantifies over every pair of charges, both source signs and every signed pair of physical lifts. It requires OriginalCompatible only when each projected ground sign matches its own lift. The ground-pair residue identity remains a premise and is not established by this extension.")),
            Paragraph(Text("The restricted word induction tracks both first signs and the parity of the second word. Its native defect transport uses the smaller right source at delta-1 and the h0 correction at gamma+1 and delta-1. The source zero mode exchanges the first projected signs with its bilinear charge coefficient, including when that coefficient is zero.")),
            Paragraph(Text("The coefficient law is linear in its right source and scalar-linear in its first source. Finite sums preserve the three individual support assertions and both ordered terms, using their actual pointwise finite supports. No uniform homogeneous target input is assumed.")),
            Paragraph(Text("For an arbitrary second source b, the sector selected by delta has a finite theta-eigensource expansion into negative current words on projected grounds. The restricted word theorem applies to every summand. Corrected-field monodromy identifies the selected physical slice with the original b slice; ordinary state-field theta covariance transports the projection through the original mu at gamma+delta. This sum lift retains the odd-odd carry.")),
            Paragraph(Text("The resulting GroundFirst law applies to every original second source and every actual tensor input under precisely SectorGroundPair and the matching first sign. Arbitrary-first transport, the ground-pair residue supplier and the full Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT programme remain incomplete. No module or Jacobi law is assumed, and no physical realization or literature novelty is claimed.")),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-sector-ground-right-word"),
                DeclarationHandle.Create(Prefix + "sector_ground_right_word"),
                H("Sector-compatible word propagation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("SectorGroundPair implies the full OriginalCompatible law for every negative current word, with the first sign equal to (-1)^gamma and the word sign equal to (-1)^delta. The h0 term is evaluated at the opposite first ground sign and at gamma+1 and delta-1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-physicalslice-sectorproject"),
                DeclarationHandle.Create(Prefix + "physicalSlice_sectorProject"),
                H("Physical slice projection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a lift delta matching eta, correctedField of sectorProject(eta,b) has exactly the same physicalSlice as correctedField of b, for all actual target inputs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-mu-sectorproject"),
                DeclarationHandle.Create(Prefix + "mu_sectorProject"),
                H("Original source projection transport"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a first eigensource of sign (-1)^gamma, projection of the original mu at the sum lift gamma+delta equals mu of the second source projected at delta. The hypotheses name both Bool signs and the sum sign explicitly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-sector-projectedground-arbitrary-second"),
                DeclarationHandle.Create(Prefix + "projectedGround_arbitrary_second"),
                H("Complete conditional GroundFirst extension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every lattice D, unit determinant witness hu, charge alpha, Bool epsilon, signed gamma and delta, and arbitrary original source b, SectorGroundPair and the exact first-sector condition imply OriginalCompatible(projectedGround(alpha,epsilon),b,gamma,delta). Every p,q,r and actual inhomogeneous input x is retained, with the three separate finite supports and both ordered terms of fullLaw."))),
                DescribeRole.Theorem))));
}
