using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalEvenExteriorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identification of the closed cosine tail with the original even exterior and its actual orthogonal projection.",
        H("Original even exterior projection"),
        Blocks(
            Paragraph(Text("All spaces and maps use complex L2 for Lebesgue measure restricted to Ioc(-a,a]. originalEven is the independently defined AE-even zero-extension sector. exteriorSpace(a,M) is the existing closed span of cosine modes M+j+1 for natural j, and exteriorProjection has that subspace as its codomain. The identifications below require a>0 and natural M; there is no terminal upper tail cutoff.")),
            Describe.Lean(
                DescribeId.Create("finite-head"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenExterior.finiteHead"),
                H("The finite head consists of modes zero through M"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex span is indexed by Fin(M+1), so the constant mode and the mode M are both included. It is finite dimensional and therefore supports its orthogonal projection. The finite head and the closed tail both lie in originalEven; for a>0 their mutual orthogonality follows from the existing physical cosine orthonormality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tail-is-original-even-exterior"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorSpace_eq_even_inf_head_orthogonal"),
                H("The closed tail is the original even head complement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and every natural M, exteriorSpace(a,M) equals originalEven(a) intersected with the orthogonal complement of finiteHead(a,M), with both subspaces in the full window carrier. For the reverse inclusion, subtract the projection onto the existing tail. The residual remains originally even and orthogonal to the head and tail. Splitting each natural cosine index at M then gives zero inner product with every mode, so original even cosine injectivity kills the residual. The full even identification is proved here using completeness, rather than built into the definition of the tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("even-projection"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenExterior.evenProjection"),
                H("Projection onto the original even sector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the original even subspace's starProjection, regarded as a continuous complex linear endomorphism of WindowL2(a). It is defined for arbitrary real a."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("head-projection"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenExterior.headProjection"),
                H("Projection onto the finite cosine head"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This starProjection is also an endomorphism of WindowL2(a), for arbitrary real a and natural M. Its codomain convention differs from the subspace-valued exteriorProjection; the following identity explicitly includes the latter's subtype inclusion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exterior-projection-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorProjection_identity"),
                H("The actual exterior projection on the full window carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and natural M, inclusion composed with exteriorProjection(a,M) equals (id-headProjection(a,M)) composed with evenProjection(a). The equality is between continuous complex linear maps on all WindowL2(a), including inputs that are not even. If e is the even projection of u and h is the head projection of e, then e-h lies in the identified tail and u-(e-h) is orthogonal to it. Uniqueness of orthogonal projection proves the equality. Omitting the even projection on an arbitrary input is not part of this statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exterior-projection-prime"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorProjection_prime"),
                H("Head subtraction for the actual symmetric prime image"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a>0, arbitrary natural M and N and arbitrary complex v, the included projection of primeHeadL2(a,N,v) equals that image minus its headProjection at M. No N<M separation is required for this identity. The even projection disappears because the exact prime image was proved to lie in originalEven, retaining every von Mangoldt prime-power term up to primeCutoff(a)=floor(exp(2*a)) and both signed compressed shifts.")),
                    Paragraph(Text("This is a standard closed-subspace and orthogonal-projection argument applied to the original analytic objects. It supplies no canonical full Weil arithmetic/operator identification, signed positivity, literature novelty or Riemann-hypothesis conclusion."))),
                DescribeRole.Theorem))));
}
