using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class MultiplicativeDigitInvariantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The contraction reading is additive on coprimes, signed by digit shape, and splits "
            + "off zeta.",
        H("Multiplicative Digit Invariant"),
        Blocks(
            Paragraph(Text(
                "Three properties of the contraction reading were proved separately and never "
                    + "stated together: additivity over coprime factors, the sign rule fixed by "
                    + "the parity of the least occupied Zeckendorf index, and the Dirichlet "
                    + "factorisation into zeta times the prime-axis series.")),
            Paragraph(Text(
                "This document adds exactly one thing: the conjunction. Each conjunct is the "
                    + "existing theorem transcribed word for word, with its implicit binders "
                    + "made explicit; nothing is weakened and nothing new is proved. The reason "
                    + "the conjunction is worth a declaration is that the source sentence is a "
                    + "single claim about one invariant, and separate parts do not stand in for "
                    + "it: what carries a compound sentence is a node, not a set of pieces.")),
            Paragraph(Text(
                "Read together the three say why the reading deserves the name invariant. It is "
                    + "additive where the prime supports are disjoint, so it is a homomorphism "
                    + "off the common factors. Its sign does not track magnitude but the parity "
                    + "of one digit position. And its Dirichlet series carries the arithmetic of "
                    + "the integers in the zeta factor while the digit structure sits entirely "
                    + "in the prime-axis factor.")),
            Describe.Lean(
                DescribeId.Create("contraction-reading-is-a-multiplicative-digit-invariant"),
                DeclarationHandle.Create(
                    "D5/S3/Axis/MultiplicativeDigitInvariant."
                        + "lambda_minus_is_a_multiplicative_digit_invariant"),
                H("The contraction reading is a multiplicative digit invariant"),
                StatementSource.FromAuthor(CoprimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed conjunct is coprime additivity; the package also carries the "
                        + "least-index sign rule and the zeta factorisation."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Axis/LambdaMinusDirichletSeries")),
        ]));

    private static Formula Lambda(Formula arg) =>
        Seq(F.Id("lambda"), Underscore, Grp(F.Id("minus")), Open, arg, Close);

    private static Formula CoprimeFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");

        return Disp(Seq(
            Forall, Sp, m, Comma, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Operatorname, Grp(F.Id("gcd")), Open, m, Comma, Sp, n, Close, Sp, Eq, Sp, D(1),
            Sp, Rightarrow, Esc,
            Lambda(Seq(m, Sp, Cdot, Sp, n)), Sp, Eq, Sp,
            Lambda(m), Sp, Plus, Sp, Lambda(n), Dot));
    }
}
