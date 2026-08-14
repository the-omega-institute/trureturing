using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.MetricGeometry;

internal sealed class GreenClassHausdorffDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The PiNat naming space and every finite-support green class have dimension log base two of the alphabet size.",
        H("Hausdorff Dimension of the Naming Space and Its Green Classes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("string-measure-mass-distribution-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.stringMeasure_le_ediam_rpow"),
                H("String measure satisfies the critical mass-distribution bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Mu, Open, F.Id("s"), Close, Sp, Leq, Sp,
                    Operatorname, Grp(F.Id("ediam")), Open, F.Id("s"), Close,
                    Caret, Grp(F.Id("d"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let n = card O and d = logb 2 n. For a non-subsingleton set s of infinite "
                        + "strings, choose the least coordinate m at which some two members differ. "
                        + "Minimality makes every string in s agree with one fixed member on the prefix "
                        + "range m, so s lies in a prefix green class of string measure n^(-m).")),
                    Paragraph(Text(
                        "The two witnesses that differ at coordinate m have PiNat distance (1/2)^m. "
                        + "Hence the extended diameter of s is at least that scale. The identity "
                        + "((1/2)^m)^d = n^(-m), obtained from 2^d = n, turns cylinder measure "
                        + "monotonicity into mu(s) <= ediam(s)^d.")),
                    Paragraph(Text(
                        "If s is subsingleton, it is contained in one point. That point lies in every "
                        + "prefix cylinder, whose masses n^(-m) tend to zero because n > 1; therefore its "
                        + "string measure, and hence the measure of s, is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-hausdorff-measure-is-string-measure"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.hausdorffMeasure_eq_stringMeasure"),
                H("Critical Hausdorff measure equals uniform string measure"),
                StatementSource.FromAuthor(Disp(Seq(
                    Mu, Underscore, Grp(F.Id("H")), Caret, Grp(F.Id("d")),
                    Sp, Eq, Sp, Mu))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The mass-distribution bound gives stringMeasure O <= mu_H[d] through Mathlib's "
                        + "le_hausdorffMeasure theorem.")),
                    Paragraph(Text(
                        "For the reverse normalization, cover the full naming space at level m by all "
                        + "prefix cylinders indexed by Fin m -> O. Every cylinder has extended diameter "
                        + "(1/2)^m, while there are n^m cylinders. Their d-dimensional costs sum exactly "
                        + "to n^m n^(-m) = 1, and the maximum diameter tends to zero.")),
                    Paragraph(Text(
                        "The finite-cover liminf bound therefore gives mu_H[d](univ) <= 1. The lower "
                        + "measure inequality gives the opposite bound because string measure is a "
                        + "probability measure. Thus critical Hausdorff measure is also a probability "
                        + "measure, and equality follows from order plus equal total mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("naming-space-hausdorff-dimension"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.dimH_univ_eq_namingDim"),
                H("The full naming space has dimension log base two of the alphabet size"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dimH")), Open, F.Id("X"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("logb")), Open, D(2), Comma, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("O"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Nontriviality gives n >= 2, so d = logb 2 n is nonnegative and can be passed to "
                        + "the Hausdorff-dimension API as a nonnegative real.")),
                    Paragraph(Text(
                        "At exponent d the Hausdorff measure of the full space equals the string measure "
                        + "of the full space, namely one. It is therefore both nonzero and finite. Mathlib's "
                        + "critical-measure characterization identifies the Hausdorff dimension with d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("green-class-hausdorff-dimension"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension.dimH_greenClass_eq_namingDim"),
                H("Every finite-support green class has full naming-space dimension"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dimH")), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("logb")), Open, D(2), Comma, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("O"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At the critical exponent, the Hausdorff measure of G(S,t) is its string measure. "
                        + "The finite-cylinder formula makes this value strictly positive, while probability "
                        + "of the ambient string measure makes it finite. The same critical-measure "
                        + "characterization therefore gives dimH G(S,t) = logb 2 (card O).")),
                    Paragraph(Text(
                        "Pinning finitely many coordinates changes the critical measure by a positive "
                        + "factor but does not reduce dimension. The varying-marginal generalization to "
                        + "nonuniform coordinate laws remains uncovered."))),
                DescribeRole.Theorem))));
}
