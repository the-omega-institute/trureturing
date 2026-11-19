using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeSectorCharacterWeilCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual dual-coset graded traces and Weil S covariance",
        H("Actual lattice-sector character S transformation"),
        Blocks(
            Paragraph(Text("For any original positive definite even integral Gram matrix, every discriminant class a uses its existing representative beta and the rational dual vector G-inverse beta. The sector is the existing auxiliary-lattice module action. Its grade at rational energy e is the literal eigenspace of the original-omega operator moduleL(D,beta,H,0), for every complex inverse H satisfying both inverse identities. The normalized character sums the identity traces on these finite grades with exp(2 pi i tau (e-rank/24)). It is not defined as a theta/eta quotient.")),
            Paragraph(Text("The existing coefficient equivalence identifies the full actual grade with its finite charge/occupation fiber. The trace equals the fiber cardinality. Absolute convergence of the Gaussian and ordinary integer-frequency occupations permits regrouping by every rational energy and factoring the resulting basis sum. The occupation product evaluates to the inverse rank-th power of eta after the vacuum shift, giving the character formula Theta_a/eta^rank. Empty grades and rank zero remain included.")),
            Paragraph(Text("The existing principal-branch theta and eta S laws cancel the common weight factor. The remaining operator is exactly weilS: the kernel is pairingCharacter(a,-b), with normalization rho(D) inverse, where rho is the positive square root of the original discriminant cardinality. No unimodularity, even-rank assumption, choice of minimum, or identification of distinct sector labels is imposed. The result concerns these actual lattice modules; Monster identification, orbifold sewing and a complete CFT construction are separate obligations.")),
            Describe.Lean(
                DescribeId.Create("lattice-sector-character-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorGrade"),
                H("Actual rational-energy grades"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D, complex matrix H, discriminant class a and rational energy e, sectorGrade is the eigenspace of moduleL(D,representative(D,a),H,0) with eigenvalue the complex cast of e. It uses the original conformal zero mode on the existing actual dual-coset carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lattice-sector-character-trace-term"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorTraceTerm"),
                H("Finite-grade identity trace terms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive real Gram matrix, every complex inverse H satisfying both inverse identities, every a, complex tau and rational e, sectorTraceTerm is the trace of the identity on sectorGrade multiplied by exp(2 pi i tau (e-rank/24)). The existing finite-dimensionality theorem supplies the finite actual grade; no trace is taken on the infinite ambient carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lattice-sector-character-value"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.sectorCharacter"),
                H("Normalized actual sector character"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same positivity and inverse hypotheses, sectorCharacter is the complex tsum of sectorTraceTerm over every rational energy. It is defined for every complex tau; absolute convergence and the transformation law are asserted on the upper half-plane."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lattice-sector-character-s-transform"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform"),
                H("Absolute convergence and the normalized sector S law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every discriminant class a and every tau in the upper half-plane, the actual rational-grade trace series is absolutely summable, and its value at -1/tau is the a coordinate of the existing Weil S operator applied to the entire vector of actual sector characters at tau. The proof derives the theta/eta formula from finite actual eigenspace traces before invoking the analytic transformation laws."))),
                DescribeRole.Theorem))));
}
