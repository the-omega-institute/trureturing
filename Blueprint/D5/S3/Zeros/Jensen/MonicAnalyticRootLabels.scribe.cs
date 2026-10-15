using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class MonicAnalyticRootLabelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simple-root monic analytic polynomial families have a covering zero graph and global analytic labels.",
        H("Monic Analytic Root Labels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monic-analytic-simple-root-projection-is-covering"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Jensen/MonicAnalyticRootLabels.monic_analytic_simple_root_projection_isCovering"),
                H("The simple-root zero graph projects as a covering"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an open complex parameter domain, assume a monic fixed-degree polynomial family whose coefficients through the degree are analytic and every root is simple. The zero graph in the parameter subtype times the complex plane projects to the parameter subtype as a covering map.")),
                    Paragraph(Text("The proof uses the finite coefficient sum for joint analyticity, the native complex implicit-function theorem for actual local root graphs, the fixed-degree monic properness theorem for compact preimages, and finite fibers. Degree zero and empty fibers are included.")),
                    Paragraph(Text("The four-slot mathematical registration evidence compiles, but the covering audit is declared_unresolved: IE-C050 ClosedTruthReadout, unclassified_form, source.unlinked_operand at Classical.choice. The missing complete source/readout binding certificate is recorded in https://github.com/the-omega-institute/trureturing/issues/16328. The kernel theorem and its full telescope are retained.")))),
            Describe.Lean(
                DescribeId.Create("monic-analytic-simple-roots-have-global-labels"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Jensen/MonicAnalyticRootLabels.monic_analytic_simple_roots_have_global_labels"),
                H("Simple roots admit globally compatible analytic labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On a simply connected open parameter subtype, the covering lifts of the identity, one for each root at a base point, produce exactly q analytic root labels indexed by Fin q. The labels are pairwise distinct and exhaust every root in every fiber; a root family analytic on the domain is uniquely determined by its base value.")),
                    Paragraph(Text("Analyticity is obtained by comparing each continuous lift with the local implicit-function branch. Complex splitting and the simple-derivative hypothesis provide exactly q distinct base roots. The theorem makes no claim about RH, Robin inequalities above 5040, signed cofactor transfer, or a uniform collar beyond the open domain.")),
                    Paragraph(Text("An exact application uses the actual exterior source E = exteriorSource Z (localTheoryCore Z T rho), its finite extraction H = extraction n E, and the normalized Appell polynomial P_t = sum from k = 0 through q of (M_t^(k)(0)/k!) D^k X^q. Here M_t(u) = exp(-chi(t) u) (1+t u/n)^n H(t/(1+t u/n))/H(t), with chi(t) = t - (t^2/n) H'(t)/H(t). The original exterior source and its zero multiplicities are preserved; this polynomial is not identified with the full literal xi Jensen row.")),
                    Paragraph(Text("One positive constant U is chosen before all zero data Z and parameters. For T at least 32, 0 < rho at most 1/8, positive q at most 512 log(T+2), and n at least 1048576 times 196609 squared times U log(T+2) T squared divided by rho squared, the application domain is the open complex ball centered at T squared with radius T rho/32. The actual closed-chart supplier gives H(t) nonzero and simple roots throughout this ball. The normalization M_t(0) = 1 gives monicity and degree q; each coefficient is analytic by the finite jet expansion. Convexity and nonemptiness supply simple connectedness. None of these premises is assumed as an already supplied global labeling.")),
                    Paragraph(Text("Applying the global-label theorem yields compatible analytic labels on this open ball, unique after their value at the center is fixed. To use each label in the actual velocity estimate, the application explicitly proves it is a root: separability and degree q give exactly q roots, and the exhaustive unique-index map from that root set into Fin q is injective and therefore surjective. Openness then gives the eventual root equation required by the actual differentiable-branch supplier.")),
                    Paragraph(Text("With the same fixed U, every label satisfies norm(b_i'(t)) at most 129/8388608 throughout the open ball. The convex mean-value theorem then gives norm(b_i(y)-b_i(x)) at most (129/8388608) norm(y-x) for any two parameters in that ball. The exact actual-source composition has passed Lean compilation and scoped statement and axiom inspection with only the standard propext, Classical.choice and Quot.sound closure; its bind-only check is transient evidence, not another retained theorem.")),
                    Paragraph(Text("The application supplies interior global labels and their quantitative variation bound. Extending labels with ambient analyticity to the closed D/32 boundary, giving a uniform collar outside it, or obtaining a global inverse coordinate with an explicit image radius requires additional proofs. The inner closed D/64 ball lies inside the stated domain. No original-core signed transmission, full xi-to-theta coefficient bridge, RH, or strict Robin inequality for all integers above 5040 is concluded.")),
                    Paragraph(Text("The global-labels audit is declared_validated with a source-equivalence certificate for the complete original telescope and the selected exhaustion readout. This status does not validate the separate covering audit.")))))));
}
