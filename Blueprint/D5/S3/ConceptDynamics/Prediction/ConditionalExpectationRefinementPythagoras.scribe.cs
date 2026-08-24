using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Prediction;

internal sealed class ConditionalExpectationRefinementPythagorasDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula measure = F.Id("mu");
        Formula target = F.Id("T");
        Formula coarse = new Formula.Subscript(F.Id("G"), F.Id("q"));
        Formula refined = new Formula.Subscript(F.Id("G"), F.Id("r"));
        Formula ambient = F.Id("Sigma");
        Formula coarseEstimate = Call("condExpL2", target, coarse);
        Formula refinedEstimate = Call("condExpL2", target, refined);
        Formula coarseRisk = SquaredL2Error(target, coarseEstimate, measure);
        Formula refinedRisk = SquaredL2Error(target, refinedEstimate, measure);
        Formula innovation = SquaredL2Distance(refinedEstimate, coarseEstimate, measure);
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula realNumbers = Seq(Mathbb, Grp(F.Id("R")));

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, universe, Comma, RowBreak, Grp(),
            measure, Colon, Sp, Call("Measure", state), Comma, RowBreak, Grp(),
            coarse, Comma, Sp, refined, Comma, Sp, ambient, Colon, Sp,
            Call("MeasurableSpace", state), Comma, RowBreak, Grp(),
            target, Colon, Sp, Call("L2", state, measure, realNumbers), Comma,
            RowBreak, Grp(),
            coarse, Sp, Subseteq, Sp, refined, Sp, Land, Sp,
            refined, Sp, Subseteq, Sp, ambient, RowBreak, Grp(),
            Rightarrow, Sp, Open,
            coarseRisk, Sp, Eq, Sp, refinedRisk, Sp, Plus, Sp, innovation,
            Close, Sp, Land, RowBreak, Grp(),
            refinedRisk, Sp, Leq, Sp, coarseRisk, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Nested conditioning sigma-algebras split squared prediction risk into later "
                + "risk and conditional-expectation innovation.",
            H("Conditional Expectation Refinement Pythagoras"),
            Blocks(Describe.Lean(
                DescribeId.Create("conditional-expectation-refinement-pythagoras"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Prediction/"
                        + "ConditionalExpectationRefinementPythagoras."
                        + "conditional_expectation_refinement_pythagoras"),
                H("Refinement splits conditional-expectation risk"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The target is a real square-integrable random variable. The coarse "
                            + "and refined measurable spaces are both sub-sigma-algebras of "
                            + "the ambient space, with the coarse one contained in the refined "
                            + "one. The two displayed estimates are Mathlib's canonical L2 "
                            + "conditional expectations.")),
                    Paragraph(Text(
                        "The refined-minus-coarse estimate is measurable for the refined "
                            + "sigma-algebra. It is therefore orthogonal to the residual after "
                            + "refined conditioning. Expanding that orthogonal sum gives the "
                            + "exact squared-norm identity; nonnegativity of the innovation "
                            + "term gives risk monotonicity.")),
                    Paragraph(Text(
                        "For real L2 functions, squared L2 norm is the integral of the squared "
                            + "error, so the public norm identity is the canonical L2 carrier "
                            + "of the source's expected-square formula."))),
                DescribeRole.Theorem))));
    }

    private static Formula SquaredL2Error(
        Formula target,
        Formula estimate,
        Formula measure) =>
        new Formula.Power(
            Seq(Grp(Call("L2Norm", Seq(target, Sp, Minus, Sp, estimate), measure))),
            Grp(D(2)));

    private static Formula SquaredL2Distance(
        Formula left,
        Formula right,
        Formula measure) =>
        new Formula.Power(
            Seq(Grp(Call("L2Norm", Seq(left, Sp, Minus, Sp, right), measure))),
            Grp(D(2)));
}
