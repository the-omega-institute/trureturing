using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotVerdict;

internal sealed class ConjugateUnboundedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var bound = Id("M");
        var naturals = Id("N");
        var reals = Id("R");

        var statement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("M"), reals)],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [new Formula.BoundVariable(FormulaIdentifier.Create("n"), naturals)],
                new Formula.Relation(
                    bound,
                    FormulaRelationOperator.LessThan,
                    new Formula.Absolute(Call("conjugateRemainder", n)))));

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotVerdict/ConjugateUnbounded.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The conjugate reading of the greedy expansion of one passes every bound.",
            H("Conjugate Unbounded"),
            Blocks(
                Paragraph(Text(
                    "Every ingredient was already proved and none is restated here. The fourth "
                        + "remainder is past the escape threshold; the greedy digits lie in the "
                        + "range the escape estimate assumes; past the threshold one step cannot "
                        + "return; and the excess above the threshold is multiplied by the "
                        + "conjugate modulus at every step. This module is the composition.")),
                Paragraph(Text(
                    "That it needed writing at all is the point. Each of those facts had been "
                        + "landed separately and each was green on its own, but the statement "
                        + "they combine to make existed only in prose. A conjunction of proved "
                        + "things is not proved until someone writes the conjunction down.")),
                Describe.Lean(
                    DescribeId.Create("the-conjugate-orbit-is-unbounded"),
                    DeclarationHandle.Create(
                        declarationPrefix + "the_conjugate_orbit_is_unbounded"),
                    H("The conjugate orbit is unbounded"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The other half of the statement is that the orbit never returns below "
                            + "the threshold after the fourth step. Neither half says anything "
                            + "about whether the digits repeat; what they give is the side of "
                            + "the contradiction that any eventual period would have to meet."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/ConjugateValuation")),
            ]));
    }
}
