using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostChargeSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-Q quartet prerequisites: LatticeBcGhostChargeSeparation",
        H("LatticeBcGhostChargeSeparation"),
        Blocks(
            Paragraph(Text("These are retained proofs from the accepted original-Q quartet source, not new mathematics produced by changing module names. The namespace remains D5.S3.VertexAlgebra.OriginalQQuartetSource. StatementSource.WithoutFormula renders declaration handles bound to the canonical scoped report, not displayed formula bodies; the source assumptions, proof bodies and noncomputable section are unchanged.")),
            Paragraph(Text("D is the original LatticeGeneratingFieldLocality.LatticeData, with arbitrary natural rank, integral symmetric Gram matrix and even diagonal. Carrier D is the finite-support sum over every integral charge of the actual complex oscillator polynomial space. State D is Carrier D tensor Fock Complex. The existing Fock, b, c, M, G, Q and J are used without replacement. No positivity, positive-energy cutoff, restricted charge spectrum, surrogate differential or assumed locality, Jacobi, spectrum or nilpotence is added. Isotropic and negative-norm charge sectors are not removed.")),
            Paragraph(Text("This retention establishes quartet prerequisites and per-mode identities, not a total K contraction, the cohomology of the full original Q, a physical no-ghost theorem, a string construction or AdS/CFT. Full-Q nilpotence is a separately previously accepted result outside this scoped graph, not imported or certified here. Wherever that separate route is invoked, both Gram-inverse equations and the rank-26 condition remain required; these are not premises of statements that do not use that route. The larger VOA/CFT/string/AdS goal remains active and open.")),
            Paragraph(Text("Native information-escape registration is unfinished under issue #15040. Mathematical kernel checking and scoped report binding do not imply declared_validated registration, frozen admission, CI, remote acceptance or independent canonical source/render approval.")),
            Paragraph(Text("oscillatorNormalSummand explicitly removes the summands with either current mode zero. The remaining statewise finite sum defines oscillatorSugawaraMode on the original charge carrier. The support argument is actual, not an assumed energy cutoff or formal divergent series.")),
            Paragraph(Text("For m nonzero and an actual charge alpha, sugawaraMode(H,m)(single(alpha,P))=a_complexCharge(alpha)(m)(single(alpha,P))+oscillatorSugawaraMode(H,m)(single(alpha,P)). The finite normal-order sum separates its two zero-current contributions, contracts each with H, and retains the oscillator remainder.")),
            Paragraph(Text("Both H*gramComplex(D)=1 and gramComplex(D)*H=1 are exact premises of inverseGram_charge_contractions and the charged separation theorem. No positivity, nonzero charge, isotropy, rank-26 assumption or m=0 separation is asserted. original_tensor_sugawara_charged_separation transports this exact result to M on the original State and is a consumed transport helper.")),
            Paragraph(Text("oscillatorNormalSummand_finite, normalSummand_finsum_split and original_sugawara_charged_separation are consumed bind-only helpers: support transport, finite-sum normalization and substitution of the existing inverse-Gram contractions respectively. ChargeSeparation earns no standalone new-content or module escape credit. First-admission and module escape remain unverified pending actual broader integration; the original proofs and hypotheses are retained unchanged.")),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-oscillatornormalsummand"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorNormalSummand"),
                H("oscillatorNormalSummand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retained original construction on the unchanged carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-oscillatornormalsummand-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorNormalSummand_finite"),
                H("oscillatorNormalSummand finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed bind-only support-subset helper using the existing normalSummand_finite result and definition normalization, not standalone new mathematical content. Retained canonical consumers: D5.S3.VertexAlgebra.OriginalQQuartetSource.oscillatorSugawaraMode and D5.S3.VertexAlgebra.OriginalQQuartetSource.normalSummand_finsum_split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-oscillatorsugawaramode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorSugawaraMode"),
                H("oscillatorSugawaraMode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retained original construction on the unchanged carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-chargescalar-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.chargeScalar_expansion"),
                H("chargeScalar expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: chosenH_original_chargeQuadratic, inverseGram_charge_contractions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-inversegram-charge-contractions"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.inverseGram_charge_contractions"),
                H("inverseGram charge contractions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: chosenH_original_chargeQuadratic, original_sugawara_charged_separation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-normalsummand-zero-mode-split"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.normalSummand_zero_mode_split"),
                H("normalSummand zero mode split"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: normalSummand_finsum_split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-normalsummand-finsum-split"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.normalSummand_finsum_split"),
                H("normalSummand finsum split"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed bind-only finite-sum splitting and normalization helper after normalSummand_zero_mode_split, not standalone new mathematical content. Retained canonical consumer: D5.S3.VertexAlgebra.OriginalQQuartetSource.original_sugawara_charged_separation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-original-sugawara-charged-separation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.original_sugawara_charged_separation"),
                H("original sugawara charged separation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed bind-only helper substituting inverseGram_charge_contractions and normalSummand_finsum_split, then normalizing sums and scalars, not standalone new mathematical content. Both Gram-inverse equations and the nonzero-mode hypothesis are unchanged. Retained canonical consumer: D5.S3.VertexAlgebra.OriginalQQuartetSource.original_tensor_sugawara_charged_separation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostchargeseparation-original-tensor-sugawara-charged-separation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.original_tensor_sugawara_charged_separation"),
                H("original tensor sugawara charged separation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_adapted_M_nonzero."))),
                DescribeRole.Theorem))));
}
