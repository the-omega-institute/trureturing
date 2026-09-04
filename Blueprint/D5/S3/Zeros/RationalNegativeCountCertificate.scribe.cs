using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class RationalNegativeCountCertificateDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/RationalNegativeCountCertificate."
            + "rational_negative_count_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty open negative-count region contains a rational parameter certificate.",
        H("Rational Negative-Count Certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("rational-negative-count-certificate"),
            DeclarationHandle.Create(Declaration),
            H("Failure in an open negative-count region has rational parameters"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let Q(q,r) be a real two-parameter counting profile. Define the "
                        + "negative-count region by r > 0, Q(q,r) > 0, and a negative "
                        + "scale-weighted radial derivative r times d/dr log Q(q,r). "
                        + "If this region is open and failure of RH makes it nonempty, then "
                        + "it contains a point with both q and r rational.")),
                Paragraph(Text(
                    "The proof applies the dense rational embedding in each real coordinate, "
                        + "uses Mathlib's product theorem for dense ranges, and extracts a "
                        + "preimage in the supplied open region. Membership gives all three "
                        + "displayed certificate inequalities at once.")),
                Paragraph(Text(
                    "The source invokes a negative open set but does not state the analytic "
                        + "hypotheses that establish openness or produce a real witness from "
                        + "failure of RH. The formal theorem exposes those two bridge facts as "
                        + "premises. Positivity of Q at the witness makes the real logarithm "
                        + "semantically nondegenerate, and strict negativity excludes the "
                        + "zero value returned by Lean's total derivative at a "
                        + "nondifferentiability point."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula TheoremFormula()
    {
        Formula prop = Call("Prop");
        Formula real = Call("Real");
        Formula rational = Call("Rat");
        Formula rh = F.Id("RH");
        Formula qProfile = F.Id("Q");
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula profileType = new Formula.TypeArrow(
            real, new Formula.TypeArrow(real, real));
        Formula region = Call("negativeCountRegion", qProfile);
        Formula bridgePremises = And(
            Call("IsOpen", region),
            Implies(new Formula.Not(rh), Call("Nonempty", region)));
        Formula certificate = Exists(
            [Bound("q", rational), Bound("r", rational)],
            And(
                Less(D(0), r),
                And(
                    Less(D(0), Call("apply", qProfile, q, r)),
                    Less(
                        Call("radialLogDerivative", qProfile, q, r),
                        D(0)))));

        return Disp(ForAll(
            [Bound("RH", prop), Bound("Q", profileType)],
            Implies(bridgePremises, Implies(new Formula.Not(rh), certificate))));
    }
}
