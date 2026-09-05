using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GermWindow;

internal sealed class GermZeroCertificateDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/GermWindow/GermZeroCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generated L2c certificate encloses all sixty-one modes at the frozen "
            + "candidate, assembles the center norm and derivative margins, and closes "
            + "the prime-two golden local-factor zero obligation.",
        H("Generated Golden Germ Zero Certificate"),
        Blocks(
            Paragraph(Text(
                "The in-repo generator tools/scripts/agent/germ_jet_certificate.py emits "
                    + "this module deterministically; --check regenerates and byte-compares "
                    + "it. Its 61-row rational table has columns termReLo/Hi, termImLo/Hi, "
                    + "derivReLo/Hi, and derivImLo/Hi for v = 0,...,60. Exact assembly gives "
                    + "center real interval [-6.898169e-12,-6.8981e-12], center imaginary "
                    + "interval [2.75425869e-10,2.75425943e-10], additive norm bound "
                    + "17645257/62500000000000000 = 2.82324112e-10, and derivative-real "
                    + "lower bound 1877338029556539187/10^18 = 1.877338029556539187.")),
            Entry(
                "sixty-mode-center-norm",
                "g60_center_norm_lt",
                CenterNormFormula(),
                "The 61-mode truncation is smaller than four times 10^{-10}",
                "The real and imaginary generated interval sums are converted by the "
                    + "frozen coordinate norm lemma. The certified 2.82324112e-10 bound "
                    + "lands below the preregistered 2.9e-10 falsifier threshold.",
                DescribeRole.Theorem),
            Entry(
                "sixty-mode-center-derivative-real-part",
                "g60_center_deriv_re_gt",
                CenterDerivativeFormula(),
                "The derivative real part exceeds 1.87",
                "Summing the sixty-one exact derivative lower endpoints gives "
                    + "1.877338029556539187, so the required strict 187/100 margin holds.",
                DescribeRole.Theorem),
            Entry(
                "prime-two-local-factor-zero-near-candidate",
                "germLocalFactor_two_has_zero_near_candidate",
                NearbyZeroFormula(),
                "The prime-two golden local factor has a nearby zero",
                "This bind-only closure combines the generated center norm and derivative "
                    + "bounds with the frozen L2a curvature theorem and the L1 center-jet "
                    + "reduction. It closes G-c: the p = 2 golden local factor has a zero "
                    + "within 10^{-8} of c approximately 0.23815 + 5.25671 i. This is the "
                    + "kernel refutation of addendum ten's claim of no cancellation in the "
                    + "window. It says nothing about RH itself.",
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/GermWindow/GermJetModeLemma")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/GermWindow/GermZeroCertificateReduction")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/GermWindow/GermZeroCertificateJet")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction")),
        ]));

    private static DocumentBlock.Describe Entry(
        string id,
        string declaration,
        Formula statement,
        string title,
        string prose,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula CenterNormFormula() =>
        Disp(Less(
            new Formula.Norm(Call("g", F.D(6, 0), F.Id("c"))),
            Fraction(F.D(4), Power(F.Seq(F.D(1, 0)), F.D(1, 0)))));

    private static Formula CenterDerivativeFormula() =>
        Disp(Less(
            Fraction(F.D(1, 8, 7), F.D(1, 0, 0)),
            RealPart(Call("deriv", Call("g", F.D(6, 0)), F.Id("c")))));

    private static Formula NearbyZeroFormula()
    {
        Formula z = F.Id("z");
        Formula radius = Fraction(F.D(1), Power(F.Seq(F.D(1, 0)), F.D(8)));
        Formula conclusion = And(
            Member(z, Call("ball", F.Id("c"), radius)),
            Equal(Call("germLocalFactor", z, F.D(2)), F.D(0)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("z", ComplexNumbers())],
            conclusion));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula RealPart(Formula value) => F.Seq(F.Re, F.Grp(value));

    private static Formula ComplexNumbers() => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
}
