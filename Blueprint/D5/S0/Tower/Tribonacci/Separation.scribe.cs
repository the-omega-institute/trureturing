using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Distinct admissible Tribonacci digit evaluations separate uniformly at their natural conjugate scale.",
            H("Quantitative Tribonacci Conjugate Separation"),
            Blocks(
                Paragraph(Text(
                    "Let beta be the existing real Tribonacci constant and let z be any "
                    + "member of the characteristic root multiset other than beta. For every "
                    + "natural Q and every two distinct length-Q admissible names u and v, "
                    + "their complex coordinates have distance at least "
                    + "sqrt(beta - 1) times norm(z)^Q. The constant is positive and independent "
                    + "of Q. Both non-Perron roots are covered.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-conjugate-uniform-separation"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Separation.conjugateCoordinate_separation"),
                    H("Uniform separation of all finite admissible layers"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The argument applies the classical Pisot algebraic-norm method; "
                            + "no research novelty is claimed. The existing general multinacci "
                            + "irreducibility theorem is reused directly. To establish nonzero "
                            + "Perron evaluation of the difference polynomial, reversal is proved "
                            + "to preserve no-111 admissibility, and its positive-power polynomial "
                            + "evaluation is related exactly to the frozen negative-power name "
                            + "value. The natural-number decoder is not this polynomial evaluation.")),
                        Paragraph(Text(
                            "The integer resultant of the Tribonacci cubic and the digit "
                            + "difference is nonzero. At the three embeddings it is the Perron "
                            + "evaluation times the squared complex norm. Its absolute value is "
                            + "therefore at least one. A geometric-sum bound on the Perron factor "
                            + "and beta times norm(z)^2 = 1 yield the stated quantitative bound.")),
                        Paragraph(Text(
                            "This is an infinite-family arithmetic estimate for every length "
                            + "and every admissible pair. It is consumed by the positive-area "
                            + "packing and synchronized-cluster proof of Tribonacci interior."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/ModelSet")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/Gaps")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/DBonacci/Irreducibility"))
            ]));
    }
}
