using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetCanonicalLawsDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticecosetcanonicallaws-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetCanonicalLaws", H("Actual conformal translations of full Hahn fields"), Blocks(
            D("projection_translation", "For positive-definite original D, arbitrary external rank and B, any complex H satisfying both H*gramComplex=1 and gramComplex*H=1, every external d and every state v in the full ambient carrier, projection_d(Tambient v)=moduleL D (B*d) H (-1)(projection_d v). This includes off-d charge fibers. Here arbitrary polynomial derivation and projected charge transport prove the identity, which supplies the target derivative identity.", DescribeRole.Theorem),
            D("translation_injection", "With the same inverse and positivity hypotheses, ambient translation of every injected original v is its injected actual moduleL(-1) plus multiplication by the transverse charge oscillator. The transverse summand is retained. This decomposes both integer derivative identities.", DescribeRole.Theorem),
            D("source_derivative", "For those hypotheses, all a,b,u,v and every rational tau, mode of the canonical field on moduleL D (B*a) H (-1)u equals minus tau times its mode tau-1 on u, evaluated on v. Native source translation contributes +schur(b,a); subtracting it from the integer derivative supplies exactly the rational shift. Off-coset modes vanish on both sides. This is the exact Lawful.source identity.", DescribeRole.Theorem),
            D("target_derivative", "For those hypotheses, all a,b,u,v and every rational tau, actual moduleL D (B*a+B*b) H (-1) acting on the field coefficient minus the coefficient on moduleL D (B*b) H (-1)v equals minus tau times the tau-1 coefficient. The transverse input correction is -schur(a,b), with the literal ordered sign. Off-coset families separately vanish. This is the exact Lawful.target identity.", DescribeRole.Theorem),
            Paragraph(Text("Classical conventions: Bakalov--Kac, math/0402315v1, section 4.1. Native residue and conformal sources retain Scott Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical realization, categorical fusion completion or string completion is claimed. The original rank may be zero; all external-rank statements also include zero.")))));
}
