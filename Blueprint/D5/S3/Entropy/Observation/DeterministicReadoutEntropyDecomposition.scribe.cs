using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class DeterministicReadoutEntropyDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Observation/DeterministicReadoutEntropyDecomposition."
            + "deterministic_readout_entropy_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A deterministic finite readout splits source entropy into retained and residual "
            + "parts, while garbling can only increase the residual.",
        H("Deterministic Readout Entropy Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-readout-entropy-decomposition"),
                DeclarationHandle.Create(Declaration),
                H("Finite deterministic readouts split entropy and order residuals"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source, fine-readout, and coarse-readout carriers are finite. The "
                            + "source mass is nonnegative and normalized, so it represents the "
                            + "finite random state in the theorem.")),
                    Paragraph(Text(
                        "The first conjunct identifies source entropy with the sum of the "
                            + "classification entropy retained by the fine readout and the "
                            + "conditional entropy remaining in its fibers.")),
                    Paragraph(Text(
                        "The equation coarse = forget composed with fine is the deterministic "
                            + "garbling premise. The second conjunct states that the fine "
                            + "readout leaves no more conditional entropy than the coarse one."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula real = F.Id("Real");
        Formula source = F.Id("X");
        Formula fineCarrier = F.Id("Fine");
        Formula coarseCarrier = F.Id("Coarse");
        Formula mu = F.Id("mu");
        Formula fine = F.Id("q0");
        Formula coarse = F.Id("q1");
        Formula forget = F.Id("r");
        Formula x = F.Id("x");

        Formula finiteInstances = And(
            Call("Fintype", source),
            And(Call("Fintype", fineCarrier), Call("Fintype", coarseCarrier)));
        Formula nonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", source)],
            LessThanOrEqual(F.D(0), Apply(mu, x)));
        Formula normalized = Equal(Call("sum", mu), F.D(1));
        Formula factors = Equal(coarse, Call("compose", forget, fine));
        Formula hypotheses = And(
            finiteInstances,
            And(nonnegative, And(normalized, factors)));

        Formula sourceEntropy = Call("shannonEntropy", mu);
        Formula retained = Call("conceptInformation", mu, fine);
        Formula fineResidual = Call("conceptResidual", mu, fine);
        Formula coarseResidual = Call("conceptResidual", mu, coarse);
        Formula decomposition = Equal(
            sourceEntropy,
            new Formula.Binary(retained, FormulaBinaryOperator.Add, fineResidual));
        Formula monotonicity = LessThanOrEqual(fineResidual, coarseResidual);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("Fine", type),
                Bound("Coarse", type),
                Bound("mu", Arrow(source, real)),
                Bound("q0", Call("Concept", source, fineCarrier)),
                Bound("q1", Call("Concept", source, coarseCarrier)),
                Bound("r", Arrow(fineCarrier, coarseCarrier)),
            ],
            new Formula.Logic(
                hypotheses,
                FormulaLogicOperator.Implies,
                And(decomposition, monotonicity))));
    }
}
