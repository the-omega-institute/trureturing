using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualConformalEnergyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two inverse-Gram identities give nonhomogeneous, weighted and fused actual energy laws.",
        H("Actual Nonhomogeneous, Weighted and Fused Energy Laws"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Write Gc=gramComplex(D). Assume exactly H*Gc=1 and Gc*H=1 with ordinary matrix "
                + "multiplication. There is no separate symmetry, positivity, grading or desired energy "
                + "hypothesis. The one-mode commutator with omega, actual L_(-1)=T, and unconditional state "
                + "differentiation give the energy identity on arbitrary states, including sums with "
                + "different charges or energies.")),
            Describe.Lean(
                DescribeId.Create("latticeactualconformalenergy-energy-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualConformalEnergy.energy_covariance"),
                H("Nonhomogeneous energy covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every actual a and integer q, [L_0,(Y(a))_q]=(Y(L_0 a))_q -(q+1)(Y(a))_q, under the "
                        + "stated inverse pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualconformalenergy-eigenstate-mode-energy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualConformalEnergy.eigenstate_mode_energy"),
                H("Explicit actual eigenstate specialization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Assume additionally ha: L_0 a=energy*a. Then [L_0,(Y(a))_q]=(energy-q-1)(Y(a))_q. The "
                        + "actual eigenvalue premise is explicit; it is not inferred for an arbitrary state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualconformalenergy-weighted-homogeneous-mode-energy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualConformalEnergy.weighted_homogeneous_mode_energy"),
                H("Weighted charged polynomial specialization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For beta a charge and p weighted homogeneous of natural degree r with weights (i,n) to "
                        + "n+1, the actual supplier proves L_0 single(beta,p)=(r+B(beta,beta)/2) single(beta,p). "
                        + "Consequently its q-mode commutator has scalar r+B(beta,beta)/2-q-1. This uses the actual "
                        + "weighted polynomial premise, not a finite grading."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualconformalenergy-fused-state-energy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualConformalEnergy.fused_state_energy"),
                H("General actual mode-product energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For arbitrary a,b and integer q, L_0 mu(a,q,b)=mu(L_0 a,q,b)+mu(a,q,L_0 "
                        + "b)-(q+1)mu(a,q,b). Evaluating nonhomogeneous energy covariance on b proves the law; "
                        + "neither state needs to be an eigenvector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualconformalenergy-fused-eigenstate-energy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualConformalEnergy.fused_eigenstate_energy"),
                H("Both explicit eigenstate premises give fused energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Assume ha: L_0 a=alpha*a and hb: L_0 b=beta*b, in addition to the same two inverse "
                        + "equations. Then L_0 mu(a,q,b)=(alpha+beta-q-1)mu(a,q,b). Both eigenvalue premises are "
                        + "retained in the exact public telescope."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI "
                + "10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and "
                + "conformal construction. Equation numbers refer to arXiv v1.")),
            Paragraph(Text("Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, supplies residue "
                + "locality and reconstruction by creative local fields, divided derivatives and nested "
                + "normal products.")),
            Paragraph(Text("The consumed Sugawara normal-ordering and commutator architecture retains Kalle Kytola, "
                + "VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4, Apache-2.0 "
                + "attribution. The actual carrier and matrix contractions are explicit. The complete "
                + "Virasoro theorem is a separately delivered supplier; these state laws do not replace it "
                + "with a partial proof.")),
            Paragraph(Text("The carrier and formal-series interfaces use pinned Mathlib revision "
                + "db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.")),
            Paragraph(Text("This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, "
                + "PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, "
                + "string theory, AdS/CFT and physical completion are not proved here.")))));
}
