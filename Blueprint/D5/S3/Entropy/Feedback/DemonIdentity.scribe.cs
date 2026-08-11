using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Feedback;

internal sealed class DemonIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Entropy/Feedback/DemonIdentity",
            "The average posterior-to-reference divergence of a finite joint law equals its mutual information plus the input-marginal divergence from the reference."),
        H("The Feedback Divergence Identity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("average-posterior-divergence-is-mutual-information-plus-input-divergence"),
                H("Average posterior divergence is mutual information plus input divergence"),
                LeanTheorem(
                    "D5/S3/Entropy/Feedback/DemonIdentity.demon_average_divergence_eq"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("P"), Colon, Sp,
                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("u"), Colon, Sp, Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, Forall, Sp, F.Id("q"), Comma, Sp,
                    D(0), Le, Sp, F.Id("P"), Sp, F.Id("q"), Close, Sp, Rightarrow, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("u"), Sp, F.Id("x"), Close, Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("klDivergence")), Open,
                    F.Id("P"), Comma, Sp,
                    Open, F.Id("x"), Comma, F.Id("y"), Close, Mapsto, Sp,
                    F.Id("u"), Open, F.Id("x"), Close, Cdot,
                    Operatorname, Grp(F.Id("marginal")), Open,
                    Open, F.Id("j"), Comma, F.Id("i"), Close, Mapsto, Sp,
                    F.Id("P"), Open, F.Id("i"), Comma, F.Id("j"), Close, Close,
                    Open, F.Id("y"), Close, Close, Eq, RowBreak,
                    Operatorname, Grp(F.Id("mutualInformation")), Open, F.Id("P"), Close, Plus,
                    Operatorname, Grp(F.Id("klDivergence")), Open,
                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("P"), Close, Comma, Sp,
                    F.Id("u"), Close,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For a finite nonnegative joint mass function P over a product index set and a "
                        + "strictly positive reference u on the first coordinate, the average of the "
                        + "posterior-to-reference relative entropies weighted by the output marginal, "
                        + "assembled here in joint form as the relative entropy of P against the product "
                        + "of u with the output marginal, equals the mutual information of P plus the "
                        + "relative entropy of the input marginal from u. The mutual information, "
                        + "marginal, and relative entropy are the repository's own definitions, so the "
                        + "displayed identity relates existing objects without introducing new ones.")),
                    Paragraph(Text(
                        "The proof works pointwise on the joint support. Where P is positive the input "
                        + "marginal, the output marginal, and the reference are all positive there, so the "
                        + "logarithm of the reference ratio splits into a mutual-information term and an "
                        + "input-divergence term; where P vanishes the weight annihilates the term. "
                        + "Summing over the second coordinate collapses the input-divergence contribution, "
                        + "because summing the joint law over that coordinate is exactly the input "
                        + "marginal.")),
                    Paragraph(Text(
                        "This is not a restatement of a library lemma. Mathlib supplies the logarithm "
                        + "product and quotient laws and the finite double-sum reindexing; the "
                        + "repository supplies relative entropy, the marginal, and mutual information. The "
                        + "identity is the load-bearing decomposition behind the feedback reading, in "
                        + "which the average gain of an observer equals the mutual information at a "
                        + "reference-matched input. It does not claim the thermodynamic accounting or the "
                        + "reference-matched corollary, only the divergence decomposition itself.")))
            )),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Entropy/MutualInformation")),
        ]));
}
