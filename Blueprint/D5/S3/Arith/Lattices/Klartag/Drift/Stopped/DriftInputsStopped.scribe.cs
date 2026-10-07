using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftInputsStoppedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftInputsStopped.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Inputs Stopped"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift inputs stopped to the stochastic ellipsoid construction.")),
            Node("claim-3", "measurable_toLp_of_coords", "measurable to Lp of coords",
                "A map into EuclideanSpace is measurable as soon as every coordinate is.", DescribeRole.Theorem),
            Node("claim-7", "measurable_symMat_chain_entry", "measurable sym Mat chain entry",
                "Entries of symMat A_k are ℱ k-measurable.", DescribeRole.Theorem),
            Node("claim-8", "measurable_matToUT_inv_chain", "measurable mat To UT inv chain",
                "V's raw value matToUT (symMat A_k)⁻¹ is ℱ k-measurable.", DescribeRole.Theorem),
            Node("claim-9", "measurableSet_tau_le", "measurable Set tau le",
                "{τ ≤ j} is ℱ j-measurable.", DescribeRole.Theorem),
            Node("claim-10", "measurableSet_lt_tau", "measurable Set lt tau",
                "{k < τ} is ℱ k-measurable — this is the cut stoppedV and stoppedSub are taken at.", DescribeRole.Theorem),
            Node("claim-11", "measurableSet_freezeIdx_eq", "measurable Set freeze Idx eq",
                "The fibres of the freeze index min k (τ − 1) are ℱ k-measurable.", DescribeRole.Theorem),
            Node("claim-12", "stronglyMeasurable_stoppedV_coord", "strongly Measurable stopped V coord",
                "hVm: each coordinate of the stopped V is ℱ k-measurable.", DescribeRole.Theorem),
            Node("claim-13", "stronglyMeasurable_stoppedSub_coeff", "strongly Measurable stopped Sub coeff",
                "hKm: the projection matrix of the stopped free subspace is ℱ k-measurable, entrywise.", DescribeRole.Theorem),
            Node("claim-14", "stronglyMeasurable_stoppedLogDet", "strongly Measurable stopped Log Det",
                "hDm: the stopped log-determinant is ℱ k-measurable. min k (τ − 1) lands in {0, …, k} and the chain is adapted, so this is a finite sum of ℱ k-branches.", DescribeRole.Theorem),
            Node("claim-17", "measurableSet_stateGood_fil", "measurable Set state Good fil",
                "hG, the hypothesis every stopped-chain theorem carries and nobody proves.", DescribeRole.Theorem),
            Node("claim-19", "measurable_step_natFil", "measurable step nat Fil",
                "The increment is adapted: ξ_j = c • coord j is natFil (j+1)-measurable.", DescribeRole.Theorem),
            Node("claim-20", "measurableSet_stateGood_step", "measurable Set state Good step",
                "hG on the path space, for the chain's own increment: no longer a hypothesis.", DescribeRole.Theorem),
            Node("claim-21", "abs_stoppedV_coord_le", "abs stopped V coord le",
                "Each coordinate of the stopped V inherits DriftStopped2.norm_stoppedV_le's bound.", DescribeRole.Theorem),
            Node("claim-22", "driftInputs_step_stopped", "drift Inputs step stopped",
                "The step field of ChainDrift.DriftInputs for the stopped chain. hpt_stopped is the pointwise inequality; H2 (StepInputs2.condExp_inner_eq_zero) kills ⟪V_k, ξ_k⟫; H3 (StepInputs2.condExp_norm_starProjection_sq) turns the quadratic term into c·v·dim K_k = (c·cstep²)·stoppedFreeDim; and condExp_step_le_cond puts errCond — the conditional representative — in the conclusion.", DescribeRole.Theorem),
            Node("claim-24", "etaAdopted_le_quarter", "eta Adopted le quarter",
                "η ≤ 1/4 at the adopted parameters: c₃ = n² is at least 1, so DriftStopped7.c3_mul_eta_le bounds η itself.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
