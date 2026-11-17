using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class CorrelationMinorNormTetrahedronDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual tetrahedral correlation-minor violations and attainment", H("Actual tetrahedral correlation-minor violations and attainment"), Blocks(
            Entry("tetra-vector-definition", "tetraVector", "tetraVector",
                "The four unit Bloch vectors are (+++), (+--), (-+-), (--+) divided by sqrt(3).", DescribeRole.Definition),
            Entry("tetra-projector-definition", "tetraProjector", "tetraProjector",
                "Actual complex qubit matrices (I+v dot sigma)/2 are built with the existing Bloch reconstruction. Alice coordinate order is I,Z,X,Y divided by sqrt(2); this only permutes the traceless coordinates.", DescribeRole.Definition),
            Entry("tetra-projector", "tetra_projector", "tetra projector",
                "Each of the four actual matrices is PSD, trace one and idempotent.", DescribeRole.Theorem),
            Entry("tetra-sum", "tetra_sum", "tetra sum",
                "The sum of the four actual qubit projectors is twice the identity.", DescribeRole.Theorem),
            Entry("tetra-flag-definition", "tetraFlag", "tetraFlag",
                "The four Bob factors are actual diagonal matrix units, embedded into every D≥4.", DescribeRole.Definition),
            Entry("omega-definition", "omega", "omega",
                "The actual state is (1-t)/4 times the sum of the four projector/flag products, plus t/(2D) times the ambient identity. This is not a scalar replacement for a state.", DescribeRole.Definition),
            Entry("omega-separable", "omega_separable", "omega separable",
                "For D≥4 and every real t in [0,1], an explicit normalized five-term decomposition proves separability using four product densities and the maximally mixed product density.", DescribeRole.Theorem),
            Entry("row-slice-definition", "rowSlice", "rowSlice",
                "Actual Bob Hermitian operators have normalized coordinates equal to the correlation rows.", DescribeRole.Definition),
            Entry("omega-correlation-rows", "omega_correlation_rows", "omega correlation rows",
                "The actual correlation rows are the real trace coordinates of the Bob slices, in every complete trace-product-normalized Bob basis.", DescribeRole.Theorem),
            Entry("omega-gram-entry", "omega_gram_entry", "omega gram entry",
                "Hermitian Parseval gives each row-Gram entry as the trace pairing of the actual row slices.", DescribeRole.Theorem),
            Entry("q0-definition", "q0", "q0",
                "The identity-row Gram coefficient is (1-t)^2/8+(2t-t^2)/(2D).", DescribeRole.Definition),
            Entry("q1-definition", "q1", "q1",
                "All three traceless-row Gram coefficients are (1-t)^2/24.", DescribeRole.Definition),
            Entry("omega-gram", "omega_gram", "omega gram",
                "The actual row Gram is exactly diag(q0,q1,q1,q1), without any finite noise discretization.", DescribeRole.Theorem),
            Entry("omega-density", "omega_density", "omega density",
                "The actual matrices are PSD and trace one throughout the full convex noise interval.", DescribeRole.Theorem),
            Entry("omega-noise", "omega_noise", "omega noise",
                "The state minus t I/(2D) is PSD. Every t>0 in the noise interval gives a positive definite state.", DescribeRole.Theorem),
            Entry("omega-marginals", "omega_marginals", "omega marginals",
                "Right retains Alice and is exactly I2/2. Left retains Bob and is (1-t)/4 times the four occupied flags plus t ID/D.", DescribeRole.Theorem),
            Entry("omega-not-fnf", "omega_not_fnf", "omega not fnf",
                "For every D≥5 and t<1, the unoccupied flag at index four proves that Bob is not maximally mixed. Thus the state is not in FNF.", DescribeRole.Theorem),
            Entry("omega-full-norms", "omega_full_norms", "omega full norms",
                "In arbitrary complete normalized local Hermitian bases, every actual finite Schatten p≥1 and infinity full-order quantity equals sqrt(q0*q1^3). The natural increasing compound and zero cases are retained.", DescribeRole.Theorem),
            Entry("fourth-threshold-squared-definition", "fourthThresholdSquared", "fourthThresholdSquared",
                "The common fourth-order proposed squared threshold is (D-1)^3/(11664 D^4).", DescribeRole.Definition),
            Entry("fourth-threshold-definition", "fourthThreshold", "fourthThreshold",
                "The original normalized alpha beta^3 expression is 1/sqrt(2D) times sqrt((D-1)/(18D)) cubed. It is also the full qubit-side fourth elementary symmetric polynomial.", DescribeRole.Definition),
            Entry("fourth-threshold-sq", "fourthThreshold_sq", "fourthThreshold sq",
                "The alpha beta^3 expression has exactly the displayed squared threshold for every D≥2.", DescribeRole.Theorem),
            Entry("tetra-energy-lower", "tetra_energy_lower", "tetra energy lower",
                "For every D≥4 and real t in [0,1], the actual squared full-order norm is at least (1-t)^8/110592.", DescribeRole.Theorem),
            Entry("tetra-uniform-violation", "tetra_uniform_violation", "tetra uniform violation",
                "Every real t in [0,1/1000] and every integer 5≤D≤8 gives a strictly positive energy exceeding the proposed threshold. The dimension split is finite, while the noise proof covers its entire real interval.", DescribeRole.Theorem),
            Entry("tetrahedral-family", "tetrahedral_family", "tetrahedral family",
                "Actual separable density states, non-FNF marginals, both original dimension conditions 2D≤16 and D≤8, and strict violation in every finite p≥1 and infinity are proved together. The theorem directly binds the operator comparison to bound(2,D,4) and the p=1 comparison to the actual fourth elementary symmetric sum over four normalized alpha/beta variables. It also retains the uniform squared margin: every norm squared is at least (4185/4096) times the proposed squared threshold. These refute only the no-FNF extensions, not the original FNF theorems.", DescribeRole.Theorem),
            Entry("tetra-attainment", "tetra_attainment", "tetra attainment",
                "For every D≥4 the actual zero-noise tetrahedral state has every full-order Schatten norm exactly 1/(192 sqrt(3)), in arbitrary normalized local bases.", DescribeRole.Theorem),
            Entry("fourth-threshold-eq-bound", "fourthThreshold_eq_bound", "fourthThreshold eq bound",
                "The threshold is exactly the repository original Theorem 3 bound(2,D,4). The original parameter and exponent conventions are retained.", DescribeRole.Theorem),
            Entry("tetra-rank-one", "tetra_rank_one", "tetra rank one",
                "The four PSD trace-one idempotent qubit projectors have actual matrix rank one. No design-existence assumption supplies this fact.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
            Blocks(Paragraph(Text(text))), role);
}
