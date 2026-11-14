using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_RingTheory_Polynomial_Subresultant_SignedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Subresultant.Signed.",
        H("Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Subresultant.Signed."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For any commutative coefficient ring and j≤m,n, signedPsc p q m n j means (-1)^((m-j).choose 2) times psc p q m n j. Thus a right-bound drop N≥n multiplies it by p.coeff(m)^(N-n). A left-bound drop M≥m multiplies it by q.coeff(n)^(M-m) and the sign (-1)^((M-m).choose 2+(M-m)*(m+n-2*j)). The sign is the sum-of-binomial-coefficients identity and the column-block permutation sign. Zero gaps and the terminal indices j=m or j=n are included.")),
        Paragraph(Text("For every ring hom f:R→+*S with R,S commutative, (map f p).natDegree≤m and (map f q).natDegree≤n, these give the exact specializations f(signedPsc p q m N j)=f(p.coeff m)^(N-n)*signedPsc (map f p) (map f (reductum q (n+1))) m n j and f(signedPsc p q M n j)=(-1)^((M-m).choose 2+(M-m)*(m+n-2*j))*f(q.coeff n)^(M-m)*signedPsc (map f (reductum p (m+1))) (map f q) m n j. Truncation is performed before specialization. Determinant and coefficient mapping, not a generic-degree or simple-root premise, justify the formulas.")))));
}
