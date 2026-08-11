using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class QuadraticResidueCounterexampleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/QuadraticResidueCounterexample",
            "The prime two refutes the unqualified quadratic-residue equivalence."),
        H("Quadratic-Residue Counterexample at Two"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("two-refutes-unqualified-quadratic-residue-equivalence"),
                H("The prime two refutes the unqualified equivalence"),
                LeanTheorem("D5/S3/PrimeForms/QuadraticResidueCounterexample.two_refutes_unqualified_quadratic_residue_equivalence"),
                Disp(Seq(Neg, Open,
                    Operatorname, Grp(F.Id("IsSquare")), Open, D(5), Sp, Colon, Sp,
                    Operatorname, Grp(F.Id("ZMod")), Sp, D(2), Close, Sp,
                    Leftrightarrow, Sp, D(2), Equiv, Pm, D(1), Esc, Open,
                    Operatorname, Grp(F.Id("mod")), Sp, D(5), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "At p = 2, five is a square modulo two, witnessed by one, "
                        + "but two is congruent to neither one nor four modulo five. "
                        + "Thus the quadratic-residue equivalence stated only with "
                        + "p unequal to five is false, and the odd-prime premise in "
                        + "the corrected criterion is necessary.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies ZMod and IsSquare. The repository's "
                        + "existing corrected criterion handles odd primes; no existing "
                        + "Mathlib or D5 declaration states this p = 2 counterexample.")))
            ))));
}
