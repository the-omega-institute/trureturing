using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ZeroPowerSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ZeroPowerSum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite complex family containing one has a bounded power sum with real part at least one.",
        H("Finite Cassel power-sum selection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-cassel-power-sum"),
                DeclarationHandle.Create(Prefix + "exists_pow_sum_re_ge_one"),
                H("A power sum with real part at least one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Zeros/revesz1988oscillation")),
                Blocks(
                    Paragraph(Text(
                        "For every n and every indexed complex family z:Fin(n)->C with an entry equal "
                        + "to one, there is an integer exponent nu with 1<=nu<=2*n+1 and "
                        + "Re(sum_i z(i)^nu)>=1. Repeated entries retain their multiplicities, and "
                        + "the other entries have unrestricted moduli.")),
                    Paragraph(Text(
                        "Delete one entry equal to one and pair each remaining entry with its complex "
                        + "conjugate. The resulting family has d=2*(n-1) entries and real power sums p(k). "
                        + "Let c(k) be the real part of its signed elementary symmetric function, so "
                        + "c(0)=1 and c(d+1)=0. Newton's identity gives "
                        + "k*c(k)=-sum_{a+b=k,a<k} c(a)*p(b). If every p(1),...,p(d+1) were negative, "
                        + "strong induction would make every c(0),...,c(d+1) positive, a contradiction. "
                        + "A nonnegative p(nu) yields a nonnegative real power sum for the remaining "
                        + "entries; restoring the designated one proves the stated bound. "
                        + "The empty remaining family includes the case n=1.")),
                    Paragraph(Text(
                        "This is the discrete Cassel step in the proof following Lemma 6 of Revesz's "
                        + "Effective oscillation theorems for a general class of real-valued remainder "
                        + "terms, printed page 488. The finite argument uses Mathlib's "
                        + "MvPolynomial.mul_esymm_eq_sum and the vanishing of elementary symmetric "
                        + "functions above the cardinality of their indexed family."))),
                DescribeRole.Theorem))));
}
