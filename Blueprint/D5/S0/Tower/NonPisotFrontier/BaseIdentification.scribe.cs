using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class BaseIdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var frontier = Id("betaThirteen");
        var older = Id("beta13");
        var frontierConj = Id("betaThirteenConjugate");
        var olderConj = Id("beta13Conjugate");

        var statement = new Formula.Logic(
            Equal(frontier, older),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Equal(frontierConj, olderConj),
                FormulaLogicOperator.And,
                new Formula.Logic(
                    Call("Irrational", frontier),
                    FormulaLogicOperator.And,
                    Call("Irrational", frontierConj))));

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/BaseIdentification.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The frontier base and the older non-Pisot base are one number, and it is irrational.",
            H("Base Identification"),
            Blocks(
                Paragraph(Text(
                    "Two modules define the positive root of the quadratic with constant term "
                        + "three, under two names, thirty hours apart. The bodies are identical, "
                        + "so the identifications hold by reflexivity. Both modules are frozen, "
                        + "so neither definition can be withdrawn; what can be done is to state "
                        + "the identity and let a machine check it, which turns a second silent "
                        + "source into an alias that would go red if the two ever diverged.")),
                Paragraph(Text(
                    "The bridge also carries something across rather than only tidying: the "
                        + "irrationality of the base was proved on the older side and is imported "
                        + "here instead of reproved, and the conjugate's irrationality follows "
                        + "from it because the conjugate is one minus the base.")),
                Describe.Lean(
                    DescribeId.Create("the-two-bases-are-one"),
                    DeclarationHandle.Create(declarationPrefix + "the_two_bases_are_one"),
                    H("The two bases are one"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The search that would have prevented the duplication is one on the "
                            + "object, the square root of thirteen or the quadratic itself, "
                            + "rather than on the name about to be introduced. Searching for a "
                            + "name you are about to write can only confirm that you have not "
                            + "written it yet."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/BetaThirteen")),
            ]));
    }
}
