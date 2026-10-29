using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class MixedIntertwinerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized two-input twisted coefficients in the actual fixed restricted dual",
        H("Normalized two-input twisted coefficients in the actual fixed restricted dual"),
        Blocks(
            Paragraph(Text("Both inputs belong to the negative eigenspace of the original actualParity on ActualTensor D hu. At rank twenty-four this is the integer conformal sector, beginning at weight two. The ground has positive actualParity and is excluded. The target is the direct sum, over all integer source weights, of the full algebraic duals of grade D d intersect fixedSpace D. No identification of this target with the original fixed source is assumed.")),
            Paragraph(Text("The standard mode I_m is the coefficient of z^(-m-1). For weights H and K, its pairing with a fixed source a is the finite sum over p<K-1 and q<H-1 of (-1)^(H+s)/(p!q!) times actualForm(L1^p v, C_a[2s] L1^q u), where s=m+1-p-2H+q. The original right orientation K_R is used; the selected ground pairing is unchanged and symmetry is not assumed. Finite extension uses the existing actualAmbientBasis, followed by restriction of both inputs to the original negative parity eigenspace.")),
            Paragraph(Text("The original rank/16 zero mode and the actual Virasoro bracket lower odd oscillator degree by two under L1. Negative odd degrees have no nonzero eigenvectors in the original tensor basis. These facts justify the finite homogeneous L1 cutoffs. The existing signed corrected-field output law and actualForm odd-grade orthogonality select the source weight H+K-m-1 for every fixed-grade test vector. Positive Gram then supplies a finite standard-mode upper bound for every pair of actual vectors.")),
            Paragraph(Text("The carrier and parity conventions are those of Frenkel, Lepowsky and Meurman, PNAS 81 (1984), pp.3257--3258, equation (5). The finite kernel construction and its proof terms are repository work, with no claim that the announcement supplies a detailed proof of this formula. The sharp homogeneous cutoff is m>H+K-1. The finite opposite action on original grade e lands in grade e+m-d+1; its dual pullback sends grade E to E+d-m-1. The full signed mixed Jacobi identity, the nonzero vacuum channel, and consumption on the actual Leech data remain unfinished. No complete intertwiner, orbifold gluing, three-twisted crossing, Monster action, full CFT, string theory or AdS/CFT result is asserted.")),
            Paragraph(Text("All-vector input translation on this same normalized coefficient is proved in MixedTranslation: I_m(L(-1)u)v equals -m I_(m-1)(u)v. The translation proof uses the original rank/16 stress and selected form, with no symmetry premise.")),
            Paragraph(Text("MixedOpposite constructs the source-linear opposite action on this same full fixed restricted dual, proves its homogeneous compatibility and all-vector lower truncation, and supplies the corresponding opposite formal field. Full mixed Jacobi for the normalized two-input coefficient remains unproved.")),
            Describe.Lean(DescribeId.Create("normalized-coefficient-pairing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_pairing"),
                H("Pairing with every actual fixed-grade test vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite original-basis extension, target L1 weight lowering and the existing ordered form orthogonality identify every homogeneous coefficient with the finite normalized double sum, including all excluded source grades."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-coefficient-truncation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_truncation"),
                H("All-vector standard-mode truncation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive original source energy and the finite supports of both actual tensor vectors give an explicit upper cutoff for standard modes. This coarse all-vector bound is separate from the sharp homogeneous bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-homogeneous-truncation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_homogeneous_truncation"),
                H("Sharp homogeneous standard-mode cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient lies in the actual fixed-source dual grade H+K-m-1. Negative source grades vanish under positive Gram, giving the exact homogeneous cutoff."))),
                DescribeRole.Theorem))));
}
