using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriDecoderComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriDecoderComparison.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite strict comparisons for the actual Schumacher-Westmoreland and ordinary Petz decoders.",
        H("Burri's Question 1"), Blocks(
            Paragraph(Text(
                "Laura Burri, Entanglement fidelity of Petz decoder for one-shot entanglement transmission, arXiv:2502.17411v1, Section 3.3, asks: "
                + "Which performs better: the SW decoder or the Petz decoder? Section 3.1 and Theorem 1 explicitly allow every density rho and CPTP noise channel. "
                + "The nonuniform state below therefore lies in the stated domain even though the numerical code examples use flat code states. "
                + "The SW decoder here means the actual Appendix A.6, A.9, A.11-A.13 construction, including its physical isometry, source eigenbases, full SVD, ancilla preparation and W. "
                + "Petz means ordinary reference-completed Petz, with the completion term proved zero by full output support in each example.")),
            Paragraph(Text(
                "Both comparisons use CanonicalEntanglementFidelity.fidelity: v(r,i) = (sqrt(rho))(i,r), P = |v><v|, "
                + "and F_e(rho,C) = Re <v|(id tensor C)(P)|v>. The two input states are different and are never identified. "
                + "The canonical_purification theorem certifies their positivity, unit trace and actual input marginal. "
                + "Forward channel action is reference first; reverse action is channel first and is transported by the proved factor swap.")),
            Entry("forward", "forward_fidelity", "The nonuniform replacement instance uses the common fidelity",
                "Here A=Fin 2, B=Fin 1, E=A times B, rho=diag(2/3,1/3). The isometry sends |i> to |0>_B |i,0>_E. "
                + "The canonical reference has amplitudes sqrt(2)/sqrt(3), 1/sqrt(3). The same normalized vector is the fixed R'A' ancilla and W=I. "
                + "With X=|psi><psi|, M=(sqrt(rho tensor sigmaE) X)^T, the correlated block of U is [[5,sqrt(2)],[-sqrt(2),5]]/(3 sqrt(3)), and its complement is identity. "
                + "BurriReplacementDecoder proves the full source SVD, M U=X/sqrt(3), the preparation identity, all Kraus normalizations, all-input ordinary Petz action and the recovered purifications. "
                + "The ordinary Petz output state is rho; the SW output state is diag(8/9,1/9). The actual fidelities are respectively 1/3 and 11/27, a strict SW gain of 2/27. "
                + "forward_vector uses the diagonal root to prove equality to the common canonical amplitude; forward_fidelity is the resulting equality for every composite channel."),
            Entry("reverse-vector", "reverse_vector", "The reverse input is the same root purification after a factor swap",
                "Here A=Fin 2, B=Fin 2 times Fin 3, E=A times B (dimension 12), and P=A times E (dimension 24). The input is rho=I/2. "
                + "Order B as (00,01,02,10,11,12). The real positive matrix Y has diagonal 3 and off-diagonal entries Y_00,10=1, Y_01,11=-1, Y_00,02=1, Y_10,12=-1, with their symmetric partners; all others vanish. "
                + "The physical Kraus matrix indexed by e=(0,(0,a)) is K_e(b,i)=Y((i,a),b)/sqrt(31); the other nine environment labels are zero. "
                + "The noise output is Y squared/62. BurriReversePetz proves its full-rank positive root, inverse root, support and full ordinary Petz action. "
                + "The common amplitude equals the reverse channel-first maximally entangled amplitude composed with the factor swap."),
            Entry("reverse-extension", "reverse_extension_factor_flip", "The actual channel extension also flips",
                "For every actual QuantumChannel and every joint matrix T, extending the channel after swapping T equals swapping the reverse channel-first tensor extension. "
                + "This equality acts on each matrix entry, including off-support inputs; it is not an assumed fidelity reduction."),
            Entry("reverse", "reverse_fidelity", "The reverse overlap is exactly the common fidelity",
                "The amplitude equality gives the corresponding rank-one density equality. Combining it with the actual extension equality and overlap_factor_flip proves equality of the two fidelity functions for every reverse composite channel. "
                + "The physical complementary state is J (Y squared/62) J-adjoint, its environment marginal has active entries (11,10,10)/31, and the source matrix is J Y diag(s,t,t,s,t,t) J-adjoint/62, with s=sqrt(11), t=sqrt(10). "
                + "BurriReverseSource and BurriReverseCompletion retain the physical marginals and roots, all 18 null coordinates of the full SVD, W, the normalized ancilla |00>, the preparation identity and all complex positive-polar completions. "
                + "For l=4,2 put D_l=sqrt((l s+3t)^2+(s-t)^2), c_l=(l s+3t)/D_l, k_l=(s-t)/D_l. "
                + "The actual SW fidelity is ((4c_4+2c_2+k_4+k_2)^2+36+(3c_4+3c_2-k_4-k_2)^2)/124. "
                + "The exact radical sum-of-squares certificate proves it is strictly below the ordinary Petz value 27/31."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Both strict directions, for every admissible completion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "The theorem certifies both common canonical input densities and the exact forward values. For every complex Uprime with Uprime Uprime-adjoint=I and M Uprime positive semidefinite, "
                        + "the literal prepared source Kraus rows are the action of a genuine channel on every physical input matrix. Its common fidelity is strictly above ordinary Petz in the forward instance and strictly below ordinary Petz in the reverse instance. "
                        + "The arbitrary completion cannot affect the physical prepared support. These are two faithful witnesses against either uniform ordering; no equality between different input states or locally named scores is used.")),
                    Paragraph(Text(
                        "Standing is bounded. Sun Woo P. Kim, Optimal recovery for quantum error correction, arXiv:2603.06520v1, Proposition 3, Eqs. 20-22 and Corollary 4, already relates CSS/Pauli Petz posterior sampling and SW squared-posterior sampling; its optimality discussion concerns thresholds. "
                        + "Raban Iten, Joseph M. Renes and David Sutter, Pretty good measures in quantum information theory, arXiv:1608.08229v2, Section 3.3 after Eq. 54, supplies the pretty-good singlet-recovery commutator criterion. "
                        + "These are prior results, not discoveries of this formalization. The checked primary sources do not supply this exact unrestricted two-instance comparison; that bounded observation is not a global priority certificate. "
                        + "This result neither compares the Question 2 Renyi lower bounds nor classifies all channels or all decoder performance."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("burri-2025-sw-petz-decoder-comparison"), ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
