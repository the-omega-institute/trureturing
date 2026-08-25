using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class PrimorialWitnessBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Coding/PrimorialWitnessBound.primorial_witness_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sufficiently large first-prime product bounds the first distinguishing-prime index.",
        H("Primorial Witness Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primorial-witness-bound"),
                DeclarationHandle.Create(Declaration),
                H("The first distinguishing prime lies in a sufficiently large prefix"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For distinct integers x and y, horizontalWitnessComplexity is the "
                            + "least positive one-based index j for which the j-th prime does "
                            + "not divide x minus y. The imported primePrefixProduct is the "
                            + "product of the first r primes.")),
                    Paragraph(Text(
                        "If the complexity exceeded r, every prime in the first r positions "
                            + "would divide the difference. Their pairwise coprimality would "
                            + "then make the entire prefix product divide that difference.")),
                    Paragraph(Text(
                        "A positive divisor of a nonzero integer has size at most the absolute "
                            + "value of that integer, contradicting the strict prefix-product "
                            + "bound."))),
                DescribeRole.Theorem))));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula r = F.Id("r");
        Formula difference = Subtract(x, y);
        Formula distinct = new Formula.Relation(
            x,
            FormulaRelationOperator.NotEqual,
            y);
        Formula productBound = new Formula.Relation(
            new Formula.Absolute(difference),
            FormulaRelationOperator.LessThan,
            Call("primePrefixProduct", r));
        Formula hypotheses = new Formula.Logic(
            distinct,
            FormulaLogicOperator.And,
            productBound);
        Formula conclusion = new Formula.Relation(
            Call("horizontalWitnessComplexity", x, y),
            FormulaRelationOperator.LessThanOrEqual,
            r);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), new Formula.Integers()),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), new Formula.Integers()),
                new Formula.BoundVariable(FormulaIdentifier.Create("r"), NaturalNumbers()),
            ],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }
}
