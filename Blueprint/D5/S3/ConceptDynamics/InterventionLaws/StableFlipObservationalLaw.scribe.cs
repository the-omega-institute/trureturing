using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionLaws;

internal sealed class StableFlipObservationalLawDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionLaws/StableFlipObservationalLaw."
            + "stable_and_flip_observational_laws_are_uniform_independent";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stable and flip Boolean structural models have the same observational law.",
        H("Stable and Flip Observational Law"),
        Blocks(Describe.Lean(
            DescribeId.Create("stable-flip-observational-law"),
            DeclarationHandle.Create(Declaration),
            H("Both observational laws are uniform and independent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The stable and flip models are the canonical Boolean structural models "
                        + "from the intervention family. A natural treatment and exogenous "
                        + "unit are sampled independently from the uniform four-point "
                        + "Boolean population.")),
                Paragraph(Text(
                    "The displayed observational mass is constructed by evaluating the model "
                        + "outcome on each source pair. Separate public clauses state the two "
                        + "uniform marginals, pointwise factorization into those marginals, and "
                        + "the exact mass of every observed pair.")),
                Paragraph(Text(
                    "Thus both structural equations induce independent uniform Bernoulli X "
                        + "and Y coordinates and the same one-quarter joint law."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula model = F.Id("M");
        Formula stable = F.Id("MStable");
        Formula flip = F.Id("MFlip");
        Formula law = F.Id("Lobs");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula otherX = F.Id("xPrime");
        Formula otherY = F.Id("yPrime");
        Formula naturalX = F.Id("x0");
        Formula unit = F.Id("u");
        Formula boolType = F.Id("Bool");
        Formula quarter = Seq(Frac, Grp(D(1)), Grp(D(4)));
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        Formula observedPair = Pair(naturalX, Call("outcome", model, unit, naturalX));
        Formula requestedPair = Pair(x, y);
        Formula massTerm = Call("if", Equal(observedPair, requestedPair), quarter, D(0));
        Formula lawConstruction = Call("sum", naturalX, Call("sum", unit, massTerm));
        Formula Joint(Formula left, Formula right) => Apply(law, model, left, right);
        Formula XMarginal() => Call("sum", otherY, Joint(x, otherY));
        Formula YMarginal() => Call("sum", otherX, Joint(otherX, y));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            law, Open, model, Comma, Sp, x, Comma, Sp, y, Close,
            Sp, Colon, Eq, Sp, lawConstruction, Comma, RowBreak, Grp(),
            Forall, Sp, model, Colon, Sp, Call("DeterministicBoolSCM"), Comma, RowBreak, Grp(),
            Open, model, Sp, Eq, Sp, stable, Sp, Lor, Sp,
            model, Sp, Eq, Sp, flip, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, x, Colon, Sp, boolType, Comma, Sp,
            XMarginal(), Sp, Eq, Sp, half, Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, Forall, Sp, y, Colon, Sp, boolType, Comma, Sp,
            YMarginal(), Sp, Eq, Sp, half, Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp, y, Colon, Sp, boolType, Comma, Sp,
            Joint(x, y), Sp, Eq, Sp, XMarginal(), Sp, Cdot, Sp, YMarginal(), Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp, y, Colon, Sp, boolType, Comma, Sp,
            Joint(x, y), Sp, Eq, Sp, quarter, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);
}
