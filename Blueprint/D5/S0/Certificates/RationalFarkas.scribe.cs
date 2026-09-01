using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class RationalFarkasDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Certificates/RationalFarkas.infeasible_of_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact nonnegative rational dual weights provide replayable infeasibility certificates for finite linear systems.",
        H("Exact Rational Farkas Certificates"),
        Blocks(Describe.Lean(
            DescribeId.Create("rational-farkas-certificate"),
            DeclarationHandle.Create(Declaration),
            H("A negative rational dual combination excludes every primal solution"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The primal system consists of finitely many exact rational inequalities A x less than or equal to b.")),
                Paragraph(Text(
                    "A certificate assigns a nonnegative rational weight to every row, annihilates every variable coefficient after weighted summation, and makes the weighted right-hand side strictly negative.")),
                Paragraph(Text(
                    "Any feasible point would make the same weighted right-hand side nonnegative. Lean checks the finite sum rearrangement and contradiction using exact ordered-field arithmetic."))),
            DescribeRole.Theorem))));
}