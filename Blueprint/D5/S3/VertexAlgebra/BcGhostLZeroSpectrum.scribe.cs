using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostLZeroSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostLZeroSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original full ghost zero stress mode is the integral weighted occupation operator over every commutative ring.",
        H("Original Ghost Zero-Mode Spectrum"),
        Blocks(
            Paragraph(Text("K is any Type in any universe with CommRing K, including rings of positive characteristic "
                + "and the zero ring. The original BcGhostFockSupport.Fock(K) is Finset(N) ->0 K. "
                + "There are no field, characteristic-zero, nontriviality, Gram inverse, rank, positivity, "
                + "nilpotence, homogeneity or finite-mode-cutoff assumptions.")),
            Paragraph(Text("For a natural site s, siteWeight(s) is (s/2 cast into Z)+2 when s is even and "
                + "(s/2 cast into Z)-1 when s is odd. Thus siteWeight(2i)=(i:Z)+2 and "
                + "siteWeight(2i+1)=(i:Z)-1. Subtraction is integral before the map to K, never "
                + "truncated natural subtraction. The weights at sites 1,3,5,0 are respectively -1,0,1,2. "
                + "For every finite subset S, energy(S) is the integer sum of siteWeight(s) over s in S. "
                + "Energy is unbounded and differs from the parity-count ghost number.")),
            Describe.Lean(
                DescribeId.Create("bcghostlzerospectrum-original-basis-action"),
                DeclarationHandle.Create(Prefix + "L_zero_single"),
                H("Actual zero stress mode on every finite-subset basis input"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every {K:Type u} [CommRing K], every S:Finset N and every scalar a:K, "
                        + "BcGhostFockSupport.L(K,0)(Finsupp.single(S,a)) equals "
                        + "(energy(S) cast from Z to K) smul Finsupp.single(S,a). The operator L is precisely "
                        + "the original statewise finite stress sum, not a new energy definition. The statement "
                        + "covers all original finite subsets and every scalar, without a grading restriction.")),
                    Paragraph(Text("The proof constructs a private diagonal comparison endomorphism E from the "
                        + "stated independent site weights. For original signed insertion and erasure on every "
                        + "finite-support superposition, [E,create(s)]=siteWeight(s)*create(s) and "
                        + "[E,annihilate(s)]=-siteWeight(s)*annihilate(s). The signs remain those of the "
                        + "original lower-occupied-site count. Weighted insertion/erasure, followed by finite "
                        + "Finsupp induction, establishes these identities on the entire original Fock carrier.")),
                    Paragraph(Text("At every original integer b mode m and c mode p this gives "
                        + "[E,b(m)]=-m*b(m) and [E,c(p)]=-p*c(p), with the integer indices cast into K. "
                        + "The original b creator boundary is m<=-2 and the c creator boundary is p<=1; "
                        + "their other branches are the original annihilators. Existing BcGhostStressCurrent "
                        + "covariance at stress mode zero gives exactly the same brackets for the actual L0. "
                        + "Hence E-L0 commutes with every original ghost mode. Existing ghost-only "
                        + "BcGhostFockCommutant.mode_commutant_scalar makes this defect scalar; E kills the "
                        + "empty subset and BcGhostVacuum.L_vacuum_annihilation kills the actual vacuum at zero, "
                        + "so that scalar is zero. No tensor-factor commutant assertion is used.")),
                    Paragraph(Text("The actual normal-pair ordering and state-dependent finite-sum licensing "
                        + "are those of the original stress-current and vacuum suppliers. The comparison "
                        + "operator E is identified with original L0; it does not replace the stress tensor "
                        + "by definition."))),
                DescribeRole.Theorem),
            Paragraph(Text("The derivation of these concrete variable site weights is repo-derived. The existing "
                + "ghost Library note supplies shifted-mode convention background, not a proved identification "
                + "of this concrete operator with a literature field or a novelty claim.")),
            Paragraph(Ref("D5/L/VertexAlgebra/eholzer1997ghost")),
            Paragraph(Text("Integer energy labels can have equal images in K. This diagonal action theorem "
                + "does not identify integer energy fibers with exact eigenspaces over arbitrary rings. "
                + "It supplies no tensor BRST energy projections, neutral-cohomology dimension, graded "
                + "cohomology decomposition, no-ghost theorem, physical spectrum or completed string/AdS result. "
                + "Those original-model goals remain open."))
        )));
}
