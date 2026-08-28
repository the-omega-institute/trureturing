using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class SharedSourcePerfectCorrelationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Information/SharedSourcePerfectCorrelation."
            + "fair_shared_source_perfect_observational_correlation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two identity observations of one fair Boolean source have conditional success "
            + "probability one after observing true and zero after observing false.",
        H("Perfect Observational Correlation from a Shared Source"),
        Blocks(Describe.Lean(
            DescribeId.Create("fair-shared-source-has-perfect-observational-correlation"),
            DeclarationHandle.Create(Declaration),
            H("A fair shared source gives perfect observational correlation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source law assigns mass one half to each Boolean value, and both X "
                        + "and Y are the identity readout of that same source. The joint event "
                        + "X = true, Y = true therefore has mass one half, equal to the X = "
                        + "true marginal, so their ratio is one.")),
                Paragraph(Text(
                    "The joint event X = false, Y = true is impossible under the shared "
                        + "identity readout, while the X = false marginal is one half. Its "
                        + "conditional ratio is therefore zero."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("u");
        Formula trueValue = F.Id("true");
        Formula falseValue = F.Id("false");
        Formula sourceLaw = Grp(
            source, Sp, Mapsto, Sp, new Formula.Fraction(D(1), D(2)));
        Formula identityReadout = Grp(source, Sp, Mapsto, Sp, source);
        Formula pairReadout = Grp(
            source, Sp, Mapsto, Sp,
            Open, source, Comma, Sp, source, Close);
        Formula trueJoint = ConceptLaw(
            sourceLaw,
            pairReadout,
            Seq(Open, trueValue, Comma, Sp, trueValue, Close));
        Formula falseTrueJoint = ConceptLaw(
            sourceLaw,
            pairReadout,
            Seq(Open, falseValue, Comma, Sp, trueValue, Close));
        Formula trueMarginal = ConceptLaw(sourceLaw, identityReadout, trueValue);
        Formula falseMarginal = ConceptLaw(sourceLaw, identityReadout, falseValue);

        return Disp(new Formula.Aligned([
            Seq(
                new Formula.Fraction(trueJoint, trueMarginal), Sp, Eq, Sp, D(1),
                Comma),
            Seq(
                new Formula.Fraction(falseTrueJoint, falseMarginal), Sp, Eq, Sp,
                D(0), Dot),
        ]));
    }

    private static Formula ConceptLaw(
        Formula sourceLaw,
        Formula readout,
        Formula value) =>
        Call("conceptLaw", sourceLaw, readout, value);
}
