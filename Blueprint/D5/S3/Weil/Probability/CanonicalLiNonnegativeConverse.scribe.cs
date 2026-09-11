using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Zeros.ActualZeroGeometryDocument;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class CanonicalLiNonnegativeConverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prove the A006 reverse implication at the original derivative-defined canonical Li coefficients.",
        H("CanonicalLiNonnegativeConverse"), Blocks(
            Describe.Lean(DescribeId.Create("canonical-li-nonnegative-implies-rh"),
                DeclarationHandle.Create("D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.canonical_li_nonnegative_implies_rh"),
                H("All positive-index canonical coefficients are nonnegative implies RH"),
                StatementSource.FromAuthor(Imp(All("n", Natural,
                    Imp(Le(Num(1), Id("n")), Le(Num(0), Call("canonicalLiCoefficient", Id("n"))))), RH)),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/flajolet2009analytic")),
                Blocks(
                    Paragraph(Text("The only premise is nonnegativity of canonicalLiCoefficient n for every natural n at least one. The conclusion is standard Mathlib RiemannHypothesis. The canonical derivative definition and the n+1 series shift are retained.")),
                    Paragraph(Text("The private positive-boundary proof follows Theorem IV.6 and item IV.13. A genuine continuation at a finite positive radius gives convergence of the recentered series past the original boundary. Scalar uniqueness and nonnegative double summation imply original-series convergence there, contradicting the radius. The finite-subset identity is proved using map_add_univ; the inconsistent later exponents on printed p.242 are not copied.")),
                    Paragraph(Text("At real x in [0,1), the original xi argument (1-x) inverse is at least one and cannot be a strict-strip zero. Thus the actual generator is analytic there. Frozen analytic continuation uniqueness identifies the series along the real segment. The resulting convergence at every NNReal r<1, including zero, feeds the frozen canonical_li_disk_summability_implies_rh theorem.")),
                    Paragraph(Text("The Li specialization is repository assembly with the cited Pringsheim argument acknowledged. This is A006 reverse only. A007 reverse may later consume it; forward positivity, strictness and the fixed-lambda1 A013 bound remain unchanged. No full equivalence atom, independent review, admission, freeze, coverage or publication is claimed by this document."))),
                DescribeRole.Theorem))));
}
