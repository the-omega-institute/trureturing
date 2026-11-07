using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Analysis;

internal sealed class OriginalHeatSmoothingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/Analysis/OriginalHeatSmoothing.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual original Hilbert vector acquires one coherent original smooth family under positive-time heat, with global Sobolev bounds and compact smoothing tails.",
        H("Original HeatSmoothing"),
        Blocks(
            Definition("heatSmoothingConstant", "heatSmoothingConstant", "Use C(t,k)=(max(1,k/t))^k for positive t. This is finite, nonnegative and equal to one at k=0. The definition is an ordinary real expression; no smoothing assertion at t=0 is supplied."),
            Paragraph(Text("The consumed heat_scalar_bound proves the global estimate for every real E>=0. For k=0 it is exp(-tE)<=1. For k>0 set a=t/k and B=max(1,k/t). Then B>=1 and B*a>=1, so 1+E<=B*(1+aE)<=B*exp(aE), using Real.add_one_le_exp. Raise to k and multiply by exp(-tE); Real.exp_nat_mul and k*a=t cancel the exponent. There is no finite numerical cutoff. finite_multiplier_bound, with source order zero, translates this into the true original norm bound for heat k t on embed k v.")),
            Definition("heatSmoothing", "heatSmoothing", "For t>0, extend the actual linear map heat k t composed with embed k from the dense original embed 0 core into Sobolev k, using LinearMap.extendOfNorm and the global bound just proved. The extension has domain the entire actual Hilbert space. It does not posit a lift as data or assume any desired smoothing law."),
            Result("heatSmoothing_embed", "heatSmoothing embed", "For every original finite v, heatSmoothing k t ht(embed 0 v) is literally embed k of the unshifted exp(-tE) finite grade sum. LinearMap.extendOfNorm_eq with the actual dense core and the global bound identifies it with heat k t(embed k v), and heat_embed supplies the exact core formula."),
            Result("heatSmoothing_bound", "heatSmoothing bound", "The operator norm of heatSmoothing k t ht is at most C(t,k), and every arbitrary original Hilbert x satisfies norm heatSmoothing x <= C(t,k)*norm x. These are the actual Mathlib dense-core extension estimates applied to the proven original weighted quadratic comparison. No finite-support assumption on x is present."),
            Result("heatSmoothing_inclusion", "heatSmoothing inclusion", "For all j<=k and t>0, inclusion j k composed with heatSmoothing k t is exactly heatSmoothing j t. The two continuous maps agree on every embed 0 v by their literal core identities and inclusion_embed, and density proves whole-space equality. Thus separate Sobolev lifts have actually been proved coherent."),
            Result("heatSmoothing_hilbert", "heatSmoothing hilbert", "At every k and t>0, inclusion 0 k after smoothing equals actual heat 0 t on the entire Hilbert completion. Conversely smoothing after inclusion 0 k equals heat k t on the entire kth Sobolev completion. The first identity uses proved coherence and the zero-order extension identity; the second uses the dense original kth-order core and inclusion_embed. Neither identity is a supplied Model field."),
            Definition("heatFamily", "heatFamily", "Map arbitrary x in the original Hilbert space to the family whose kth component is heatSmoothing k t ht x. heatSmoothing_inclusion is precisely the existing smoothFamilies membership predicate for every j,k,hjk. Pointwise linearity makes this an actual linear map into the existing M.Smooth; no new smooth carrier is defined."),
            Result("heat_smoothDomain", "heat smoothDomain", "Evaluation of this specific coherent family equals actual heat 0 t x, and hence heat 0 t x belongs to the existing smoothDomain=evaluation.range. The same heatFamily is the range witness. The membership assertion retains every arbitrary Hilbert vector x and strictly positive time."),
            Paragraph(Text("The consumed heatSmoothing_split proves S_k(t)=T_k(t/2) composed with S_k(t/2). On embed 0 v the extension identities reduce this to the actual semigroup addition law, and the dense original core gives equality everywhere. This factorization uses bounded maps and proves no unbounded-generator statement.")),
            Definition("heatSmoothingTruncation", "heatSmoothingTruncation", "For each N use heatTruncation k (t/2) N composed with heatSmoothing k (t/2). The split identity proves this is literally original truncation k {0,...,N} after full smoothing at t."),
            Result("heatSmoothing_tail", "heatSmoothing tail", "The smoothing approximant is the literal original grade truncation, its range is contained in cutoffSpace k N and is finite dimensional. Its operator-norm H0-to-Hk tail is bounded by C(t/2,k)*exp(-t*(N+1)/2). Factor the difference into the actual kth-order heat tail at t/2 composed with smoothing at t/2, then combine opNorm_comp_le, heat_tail_bound and heatSmoothing_bound. This bound is global, with the original metric and every finite integer cutoff."),
            Result("heatSmoothing_compact", "heatSmoothing compact", "Positive-time smoothing is compact by the split identity, actual positive-time heat_compact at t/2, and Mathlib IsCompactOperator.comp_clm. No new generic norm-limit compactness proof is introduced. The quantitative approximants and bounds are provided separately by heatSmoothing_tail."),
            Paragraph(Text("Original lattice/Hm/Sugawara attribution, Mathlib Apache-2.0 completion/extension/compactness sources, PhysLean eigenbasis source and Scott Armstrong semigroup material remain as documented in OriginalEnergyBasis and OriginalHeat. The result concerns positive-time bounded heat on the original completions and its coherent smooth lift.")))));
    private static DocumentBlock.Describe Result(string name, string title, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("originalheatsmoothing-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()),
            DescribeRole.Theorem);
    private static DocumentBlock.Describe Definition(string name, string title, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("originalheatsmoothing-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()),
            DescribeRole.Definition);
}
