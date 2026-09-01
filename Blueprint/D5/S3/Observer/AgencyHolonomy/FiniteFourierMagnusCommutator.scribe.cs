using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class FiniteFourierMagnusCommutatorDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/FiniteFourierMagnusCommutator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expand a finite Fourier generator commutator with the frozen slot kernel.",
        H("Finite Fourier Magnus Commutator"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-fourier-algebra-generator-commutator-expansion"),
            DeclarationHandle.Create(
                Prefix + "finite_fourier_algebra_generator_commutator_expansion"),
            H("Fourier commutator expansion"),
            StatementSource.FromAuthor(CommutatorFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite family in a complex associative algebra, the commutator of "
                        + "the Fourier syntheses at two times is the double sum of ordered "
                        + "algebra products weighted by the alternating slot kernel.")),
                Paragraph(Text(
                    "This closes the finite algebraic coefficient bridge to a second Magnus "
                        + "term. It does not construct a time-ordered exponential, a Bochner "
                        + "integral, or an infinite-frequency operator."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
        ]));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(FormulaIdentifier name, params Formula[] arguments) =>
        new Formula.FunctionCall(name, [.. arguments]);

    private static Formula CommutatorFormula()
    {
        Formula generator = F.Id("G");
        Formula frequency = F.Id("omega");
        Formula time1 = F.Id("t1");
        Formula time2 = F.Id("t2");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        FormulaIdentifier synthesis = FormulaIdentifier.Create("HG");
        FormulaIdentifier commutator = FormulaIdentifier.Create("comm");
        FormulaIdentifier kernel = FormulaIdentifier.Create("K");
        Formula frequencyP = Apply(frequency, p);
        Formula frequencyQ = Apply(frequency, q);
        Formula generatorP = Apply(generator, p);
        Formula generatorQ = Apply(generator, q);
        Formula sum = new Formula.Subscript(Sum, Seq(p, Comma, Sp, q));
        Formula weightedProduct = Seq(
            Call(kernel, frequencyP, frequencyQ, time1, time2),
            Sp, Times, Sp, generatorP, generatorQ);
        Formula left = Call(
            commutator,
            Call(synthesis, time1),
            Call(synthesis, time2));
        Formula right = Seq(sum, Sp, weightedProduct);

        return Disp(new Formula.Relation(
            left, FormulaRelationOperator.Equal, right));
    }
}
