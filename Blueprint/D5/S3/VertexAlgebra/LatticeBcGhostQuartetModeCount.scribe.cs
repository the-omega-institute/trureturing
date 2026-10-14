using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostQuartetModeCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-Q quartet prerequisites: LatticeBcGhostQuartetModeCount",
        H("LatticeBcGhostQuartetModeCount"),
        Blocks(
            Paragraph(Text("These are retained proofs from the accepted original-Q quartet source, not new mathematics produced by changing module names. The namespace remains D5.S3.VertexAlgebra.OriginalQQuartetSource. StatementSource.WithoutFormula renders declaration handles bound to the canonical scoped report, not displayed formula bodies; the source assumptions, proof bodies and noncomputable section are unchanged.")),
            Paragraph(Text("D is the original LatticeGeneratingFieldLocality.LatticeData, with arbitrary natural rank, integral symmetric Gram matrix and even diagonal. Carrier D is the finite-support sum over every integral charge of the actual complex oscillator polynomial space. State D is Carrier D tensor Fock Complex. The existing Fock, b, c, M, G, Q and J are used without replacement. No positivity, positive-energy cutoff, restricted charge spectrum, surrogate differential or assumed locality, Jacobi, spectrum or nilpotence is added. Isotropic and negative-norm charge sectors are not removed.")),
            Paragraph(Text("This retention establishes quartet prerequisites and per-mode identities, not a total K contraction, the cohomology of the full original Q, a physical no-ghost theorem, a string construction or AdS/CFT. Full-Q nilpotence is a separately previously accepted result outside this scoped graph, not imported or certified here. Wherever that separate route is invoked, both Gram-inverse equations and the rank-26 condition remain required; these are not premises of statements that do not use that route. The larger VOA/CFT/string/AdS goal remains active and open.")),
            Paragraph(Text("Native information-escape registration is unfinished under issue #15040. Mathematical kernel checking and scoped report binding do not imply declared_validated registration, frozen admission, CI, remote acceptance or independent canonical source/render approval.")),
            Paragraph(Text("For frequency n, etaSite is 1 at n=0 and 2(n-1) otherwise; thetaSite=2n+5. ghostBlock(n)=c(-(n+1))b(n+1)+b(-(n+1))c(n+1) is computed on the original signed polarized basis. Its eigenvalue is the sum of the two membership indicators at thetaSite and etaSite, with the n=0 polarization treated explicitly.")),
            Paragraph(Text("For any frame and axes x,y assume exactly <frame(y),frame(row)>_G=delta(row,x) and <frame(x),frame(row)>_G=delta(row,y) for every row. No inverse frame, positivity, Gram inverse, selected charge, selected energy or extra differential is assumed by original_K_block_count.")),
            Paragraph(Text("On single(alpha,coordinateSub(frame,monomial(powers,scalar))) tensor downWord S down, normalKAtom(n+1)+normalKAtom(-(n+1)) is scalar multiplication by powers(x,n)+powers(y,n)+indicator(thetaSite(n) in S)+indicator(etaSite(n) in S). This is one paired mode block, not a proved sum over all blocks or a total K eigenspace/cohomology contraction. The formula permits zero scalar, arbitrary integral charge and all finite exponents and subsets.")),
            Paragraph(Text("The unconsumed original_Q_polarized_coordinate_consumer summary is omitted only as an inadmissible delivery wrapper. Its accepted original theorem and kernel archive remain unchanged. The substantive signed ghost and bosonic per-mode counts and their original hypotheses remain canonical.")),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-etasite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.etaSite"),
                H("etaSite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retained original construction on the unchanged carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-thetasite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.thetaSite"),
                H("thetaSite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retained original construction on the unchanged carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-ghostblock"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.ghostBlock"),
                H("ghostBlock"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retained original construction on the unchanged carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-sign-erase-self"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.sign_erase_self"),
                H("sign erase self"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_site_number."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-sign-square"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.sign_square"),
                H("sign square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed bind-only helper, not a separately new mathematical result. Exact retained canonical consumers: D5.S3.VertexAlgebra.OriginalQQuartetSource.original_site_number and D5.S3.VertexAlgebra.OriginalQQuartetSource.original_site_hole_number. Consumer identity is the fully qualified constant, not a matching short name."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-original-site-number"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.original_site_number"),
                H("original site number"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: ghostBlock_original_basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-original-site-hole-number"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.original_site_hole_number"),
                H("original site hole number"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: ghostBlock_original_basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-ghostblock-original-basis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.ghostBlock_original_basis"),
                H("ghostBlock original basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retained substantive original proof; canonical naming supplies no additional mathematical novelty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-coordinatederivative-axis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.coordinateDerivative_axis"),
                H("coordinateDerivative axis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: directionalCurrent_positive_transverse_zero, original_bosonic_mode_number."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-original-bosonic-mode-number"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.original_bosonic_mode_number"),
                H("original bosonic mode number"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_K_block_count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostquartetmodecount-original-k-block-count"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostQuartetModeCount.original_K_block_count"),
                H("original K block count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Retained substantive original proof; canonical naming supplies no additional mathematical novelty."))),
                DescribeRole.Theorem))));
}
