using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class ConditionalLogicalImpurityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero conditional pair impurity characterizes fiberwise target constancy.",
        H("Zero Conditional Logical Impurity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("concept-fiber-mass"),
                DeclarationHandle.Create(DeclarationPrefix + "conceptFiberMass"),
                H("Concept fiber mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mass of a concept fiber is constructed by summing the source "
                        + "probability mass over states with the selected concept coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pair-disagreement-mass"),
                DeclarationHandle.Create(DeclarationPrefix + "pairDisagreementMass"),
                H("Pair disagreement mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pair cost sums the mass of ordered state pairs in one concept "
                        + "fiber whose target readouts differ."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-logical-impurity"),
                DeclarationHandle.Create(DeclarationPrefix + "conditionalLogicalImpurity"),
                H("Conditional logical impurity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each fiber pair-disagreement mass is normalized by its fiber mass, "
                        + "and these contributions are summed over concept coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-impurity-iff-fiber-ae-constant"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zero_impurity_iff_fiber_ae_constant"),
                H("Zero impurity exactly characterizes support-level constancy"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Almost-everywhere constancy is stated directly for the discrete "
                            + "probability law: every supported state in a positive-mass "
                            + "concept fiber has one common target value.")),
                    Paragraph(Text(
                        "The forward direction selects a supported state in each positive "
                            + "fiber and uses zero pair cost against every other supported "
                            + "state. The reverse direction makes every disagreement term "
                            + "vanish, including on zero-mass fibers."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("B");
        Formula targetCarrier = F.Id("A");
        Formula mu = Mu;
        Formula concept = F.Id("C");
        Formula target = F.Id("T");
        Formula b = F.Id("b");
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        Formula fiberMass = Call("conceptFiberMass", mu, concept, b);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coordinate, Comma, Sp, targetCarrier,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            mu, Colon, Sp, Operatorname, Grp(F.Id("PMF")), Open, state, Close,
            Comma, Sp, concept, Colon, Sp, state, Sp, To, Sp, coordinate,
            Comma, Sp, target, Colon, Sp, state, Sp, To, Sp, targetCarrier,
            Comma, RowBreak, Grp(),
            Call("conditionalLogicalImpurity", mu, concept, target), Sp, Eq, Sp, D(0),
            Sp, Iff, RowBreak, Grp(),
            Forall, Sp, b, Comma, Sp, fiberMass, Sp, Neq, Sp, D(0),
            Sp, Rightarrow, Sp, Exists, Sp, t, Comma, RowBreak, Grp(),
            Forall, Sp, x, Comma, Sp,
            Open, concept, Open, x, Close, Sp, Eq, Sp, b, Sp, Land, Sp,
            mu, Open, x, Close, Sp, Neq, Sp, D(0), Close,
            Sp, Rightarrow, Sp, target, Open, x, Close, Sp, Eq, Sp, t, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
