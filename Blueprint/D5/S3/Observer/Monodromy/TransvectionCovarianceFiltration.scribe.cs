using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class TransvectionCovarianceFiltrationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Monodromy/TransvectionCovarianceFiltration.variance_layer_eq_pair_band";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact second-moment measurement space of all bounded signed pulse "
            + "histories is a paired-reachability band, which differs from the "
            + "one-endpoint graph ball controlling first moments.",
        H("Exact Covariance Observation Filtration"),
        Blocks(
            Paragraph(Text(
                "Let K be a field with 2 nonzero, I a finite index type with "
                    + "decidable equality, H any I-by-I matrix and a a fixed sensor. "
                    + "Reuse increment from the existing Lie-filtration module. "
                    + "Set P_i(t)=1+t increment(transpose(H),i). These are the actual "
                    + "dual matrices in the ell=H x coordinates. Start with E_aa "
                    + "and act by congruences X -> P_i(t) X transpose(P_i(t)), "
                    + "using only t=+1 or -1. An effect of a word is the resulting "
                    + "rank-at-most-one quadratic measurement matrix. varianceLayer(k) "
                    + "is the linear span of all actual effects of words of length "
                    + "at most k, including the empty word.")),
            Paragraph(Text(
                "Independently define an ordered pair process starting at (a,a). "
                    + "At each step a pair may stay, either endpoint may follow "
                    + "one nonzero H entry, or a coincident pair (u,u) may move "
                    + "together along one edge to (i,i). pairBand(k) is the span "
                    + "of D_uv=E_uv+E_vu for pairs reachable in k padded steps. "
                    + "No covariance measurement or matrix-product condition "
                    + "is included in this reachability definition.")),
            Describe.Lean(
                DescribeId.Create("variance-layer-eq-pair-band"),
                DeclarationHandle.Create(Declaration),
                H("Actual bounded variance measurements equal the paired graph band"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural k, varianceLayer(H,a,k)=pairBand(H,a,k). "
                            + "There is no invertibility, alternating-form, graph "
                            + "connectedness or generic-weight hypothesis. This also "
                            + "covers singular directed matrices. Interpreting arbitrary "
                            + "covariance coordinates as physical quadratures is a "
                            + "separate specialization requiring real nonsingular "
                            + "alternating H and a bosonic CCR representation.")),
                    Paragraph(Text(
                        "The proof computes a genuine congruence: P_i(t)D_uv P_i(t)^t "
                            + "equals D_uv+t H_ui D_iv+t H_vi D_ui+t squared H_ui H_vi D_ii. "
                            + "Taking the difference of the +1 and -1 experiments isolates "
                            + "the odd part; taking their sum minus twice the old effect "
                            + "isolates the even part. A diagonal pair consequently moves "
                            + "together in one step. To isolate a split endpoint, a possible "
                            + "second nonzero coefficient is handled using the already "
                            + "available diagonal direction, rather than assuming its absence.")),
                    Paragraph(Text(
                        "A strengthened induction on independent pair reachability "
                            + "constructs each cross effect and both endpoint diagonal "
                            + "effects from actual signed histories. Separately, span "
                            + "induction shows every congruence stays in the next paired "
                            + "band, and word induction bounds every actual measurement. "
                            + "These prove the two inclusions. Auxiliary arguments are "
                            + "internal have statements; the module exports one theorem.")),
                    Paragraph(Text(
                        "For symmetric covariance matrices, trace pairing with these "
                            + "effects implies agreement of all bounded-history variances "
                            + "exactly when all reachable covariance entries agree. "
                            + "For an undirected graph the earliest pair depth has the "
                            + "ordinary formula min_b[d(a,b)+d(b,u)+d(b,v)]. The trace-kernel "
                            + "corollary, shortest-tree interpretation, physical Gaussian "
                            + "state witnesses and sample-count lower bounds are ordinary "
                            + "deductions in the research text, not additional Lean "
                            + "declarations claimed by this source.")),
                    Paragraph(Text(
                        "The bosonic protocol measures a final homodyne distribution "
                            + "on separately prepared copies after chosen quadratic controls. "
                            + "It is not sequential noninvasive observation of one unknown "
                            + "copy. Gaussian states are determined by first and second "
                            + "moments; this statement does not extend to arbitrary "
                            + "non-Gaussian density operators. Exact information completeness "
                            + "is distinct from finite-shot confidence and calibration stability.")),
                    Paragraph(Text(
                        "External context: Hjalmar Rall, Gaussian Dynamical Quantum "
                            + "State Tomography, arXiv:2602.18044v1, studies a fixed "
                            + "homogeneous Gaussian evolution with one homodyne sensor. "
                            + "Chan Roh and coauthors, arXiv:2603.21380v1, study physical "
                            + "multimode covariance reconstruction from homodyne data. "
                            + "The present statement instead allows switched signed "
                            + "rank-one controls and gives every exact graph-indexed "
                            + "measurement layer. Neither Gaussian tomography itself "
                            + "nor standard covariance polarization is claimed as new."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement() => Disp(Seq(
        Call("FieldOfCharacteristicNotTwo", F.Id("K")), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("H"), Comma, Sp, F.Id("a"), Comma, Sp, F.Id("k"), Comma, Sp,
        new Formula.Relation(Call("varianceLayer", F.Id("H"), F.Id("a"), F.Id("k")),
            FormulaRelationOperator.Equal,
            Call("pairBand", F.Id("H"), F.Id("a"), F.Id("k")))));
}
