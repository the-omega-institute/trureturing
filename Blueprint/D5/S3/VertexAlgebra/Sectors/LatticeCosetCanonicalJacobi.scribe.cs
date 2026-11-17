using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetCanonicalJacobiDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticecosetcanonicaljacobi-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalJacobi." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetCanonicalJacobi", H("Charged mixed Jacobi at every rational mode"), Blocks(
            D("mixed_jacobi", "For positive-definite original D, arbitrary external rank, integral B and external a,b, all original acting h, source u, input v, all integers p,r and every rational mode tau, mixedLeft, mixedFirst and mixedSecond each have finite support on natural i, and the first sum equals the second minus the third. Their exact weights are integerBinomial(p,i), (-1)^i integerBinomial(r,i) and the literal integral sign (-1)^r in the second ordered product. Their actions are the existing modules with labels B*a, B*b and B*a+B*b. No charged-state restriction, common support assumption or leading-term condition is imposed. Here three finite supports descend independently from the full native Borcherds theorem. On every off-coset rational mode each family separately vanishes. This supplies the Jacobi component of canonical_lawful.", DescribeRole.Theorem),
            Paragraph(Text("Classical conventions: Bakalov--Kac, math/0402315v1, section 4.1. Native residue and conformal sources retain Scott Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical realization, categorical fusion completion or string completion is claimed. The original rank may be zero; all external-rank statements also include zero.")))));
}
