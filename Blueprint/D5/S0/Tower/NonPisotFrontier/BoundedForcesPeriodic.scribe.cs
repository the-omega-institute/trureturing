using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class BoundedForcesPeriodicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var c = Id("c");
        var n = Id("n");
        var p = Id("p");
        var N = Id("N");
        var r = Id("r");
        var reals = Id("R");
        var naturals = Id("N");

        var hypothesis = new Formula.Relation(
            Num(1), FormulaRelationOperator.LessThan, new Formula.Absolute(c));

        var conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), naturals)],
            new Formula.Logic(
                new Formula.Relation(N, FormulaRelationOperator.LessThanOrEqual, n),
                FormulaLogicOperator.Implies,
                Equal(Call("r", Add(n, p)), Call("r", n))));

        var statement = new Formula.Logic(
            hypothesis, FormulaLogicOperator.Implies, conclusion);

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/BoundedForcesPeriodic.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "A bounded orbit under an expanding multiplier is zero, so periodic digits make the "
                + "remainders repeat with the same period.",
            H("Bounded Forces Periodic"),
            Blocks(
                Paragraph(Text(
                    "Two sequences driven by the same digits from some index onward differ by "
                        + "something that is multiplied by the base at every step. If the "
                        + "sequences are bounded, that difference cannot grow, and under an "
                        + "expanding multiplier the only bounded orbit is the zero one. So the "
                        + "difference vanishes and the sequence repeats.")),
                Paragraph(Text(
                    "The multiplier is arbitrary, so the same statement applies on both sides of "
                        + "the conjugation: at the base, where remainders are confined to the "
                        + "unit interval, and at the conjugate, where the bound has to come from "
                        + "somewhere else.")),
                Describe.Lean(
                    DescribeId.Create("periodic-digits-force-periodic-orbit"),
                    DeclarationHandle.Create(
                        declarationPrefix + "periodic_digits_force_periodic_orbit"),
                    H("Periodic digits force a periodic orbit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Boundedness is a hypothesis here, not a conclusion. Supplying it for the "
                            + "greedy remainders is immediate; supplying it on the conjugate side "
                            + "is exactly what the escape estimate denies, and that opposition is "
                            + "the point of the chain this module belongs to."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/BetaThirteen")),
            ]));
    }
}
