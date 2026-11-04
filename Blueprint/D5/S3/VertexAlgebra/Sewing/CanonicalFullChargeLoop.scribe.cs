using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sewing;

internal sealed class CanonicalFullChargeLoopDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An absolutely convergent ordinary positive-lattice two-insertion loop over all charges and occupations, identified with actual finite full-energy grade traces.",
        H("Full-charge canonical loop and finite-energy traces"),
        Blocks(
            Paragraph(Text("D is the original integral even symmetric lattice datum. Charges are all functions Fin(rank(D)) to Z, and occupations are all finitely supported functions on Fin(rank(D)) times N to N. The carrier, monomial b(d), canonical fields and Y are the original lattice constructions. Write Q(beta)=bilinear(D,beta,beta)/2, N(d)=oscillatorEnergy(d), and E(beta,d)=Q(beta)+N(d). The sole geometric hypothesis is positivity of the real Gram matrix. It gives Q(beta) nonnegative and makes every full-energy fiber finite, including rank zero. No determinant-unit, unimodularity, integral inverse, charge cutoff, occupation cutoff or assumed convergence is required.")),
            Describe.Lean(DescribeId.Create("full-charge-loop-term"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop.loopTerm"),
                H("Literal charge cycle and total-energy modes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For z=(beta,d,e), put gamma=-a+beta, E0=E(beta,d) and E1=E(gamma,e). The term is q1^(Q(beta).toNat+N(d)) q2^(Q(gamma).toNat+N(e)) times the d coefficient of canonical(D,a,gamma,u,r+E1-E0,b(e)) times the e coefficient of canonical(D,-a,beta,v,s+E0-E1,b(d)). The right field goes from beta to gamma; the left returns to beta. These are coordinate coefficients, with the original cocycle factors and no pairing or factorial renormalization."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-charge-loop-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop.full_charge_loop_summable"),
                H("Joint absolute convergence over all three internal indices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real-positive original Gram matrix, arbitrary fixed inserted charge a, finite oscillator polynomials u,v, signed r,s and complex q1,q2 of norm below one, the norms of loopTerm are summable jointly over beta and both occupations d,e. Zero radii, zero inserted polynomials, neutral inserted charge and rank zero are included.")),
                    Paragraph(Text("The finite occurrence list supplies the charge estimate. Set R(beta)=product_i(1+norm(beta_i)). Each coordinate norm is at most R(beta), and the norm of bilinear(unitCharge(i),beta) is at most the i-th absolute Gram row sum times R(beta). Each factor of the literal mixedConstant at sector delta+beta is therefore at most a fixed nonnegative factor times R(beta). Induction gives mixedConstant at most chargeConstant times R(beta)^(length of the occurrence list). All constants are independent of beta, both occupations and every signed mode. Creation and translation parameters A,T are chosen from a alone, and also bound -a.")),
                    Paragraph(Text("The exact mixed_descendant_bound then bounds each word coefficient by this charge polynomial, an occupation-energy polynomial and the original mixedEnvelope. The cyclic_envelope_summable theorem supplies one summable occupation majorant independent of beta. Enlarging each radius inside the open disk absorbs the finite descendant occupation powers. The actual finite canonical coefficient expansions reduce arbitrary u,v to finitely many occurrence-list pairs.")),
                    Paragraph(Text("Original quadratic_coercive bounds Q(beta) below by a positive constant times the sum of the coordinate squares. A positive auxiliary radius strictly larger than norm(q1) converts its charge weight into a Gaussian, including q1=0. Finite binomial expansion and Mathlib's integer Gaussian moment theorem make R(beta)^L times that Gaussian summable in every finite rank. Nonnegative product summability combines this charge bound with the common occupation bound. The second original charge weight is at most one for the estimate; both charge weights remain in the stated family."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-energy-block"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop.energyBlock"),
                H("Compression of an actual original field mode"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural energies n,m, energyBlock(D,a,u,r,n,m) maps the original grade m to grade n by applying Y(inclusion(a,u)) at the mode r+m-n and then the original gradeProjection n. Its codomain is established by gradeProjection_mem. The map is constructed from the field and projections before any trace or coefficient sum is taken."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-energy-block-trace"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop.blockTrace"),
                H("Trace of the two actual compressed blocks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("blockTrace(D,a,u,v,r,s,n,m) is LinearMap.trace on the original grade n of energyBlock(D,a,u,r,n,m) composed with energyBlock(D,-a,v,s,m,n). Positive real Gram guarantees finite dimension of these full grades. The trace does not act on the infinite ambient carrier."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-charge-loop-trace"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop.full_charge_loop_trace"),
                H("Unrestricted energy regrouping equals the finite-grade trace series"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same hypotheses, the double family q1^n q2^m blockTrace(n,m) is absolutely summable, and its unrestricted sum equals the unrestricted sum of loopTerm over beta,d,e. Positivity proves E(beta,d).toNat=Q(beta).toNat+N(d), so no negative energy is silently truncated.")),
                    Paragraph(Text("The original gradeBasis is indexed by every charge and occupation in the exact finite energy fiber. Its coordinates are the literal carrier coefficients. Projection retains precisely the coefficients at its target energy. inclusion_canonical and charge homogeneity identify the two matrix entries with the original canonical coefficients and force the intermediate charge to be -a+beta. trace_eq_matrix_trace and finite matrix multiplication give the exact finite energy-fiber cyclic identity. Absolute summability permits passage from the full charge cycle to the supported pair of labels, then regrouping by both original total energies. No conditionally convergent rearrangement is used.")),
                    Paragraph(Text("The Y convention is the coefficient of z^(-k-1). For homogeneous insertions of weights w_u,w_v, the choices r=w_u-1 and s=w_v-1 retain their grade blocks. For arbitrary finite inhomogeneous u,v, fixed r,s select the corresponding insertion-weight components. Replacing the displayed total-energy offsets by fixed oscillator-only offsets would describe a different family.")),
                    Paragraph(Text("The lattice and normal-product definitions retain the Bakalov--Kac, Matsuo--Nagatomo and Carnahan source attributions. The cyclic occupation contraction, original coercivity and full-grade basis are reused; Gaussian moments and finite-dimensional trace algebra come from Mathlib. This result concerns ordinary positive even lattice chiral fields. It asserts neither a reflection character nor Hilbert-space trace class, inserted modular covariance, full torus sewing, nonchiral CFT, Monster completion, string consistency or an AdS/CFT correspondence."))),
                DescribeRole.Theorem)
        )));
}
