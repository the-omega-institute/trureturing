using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identity;

internal sealed class ConceptRelativeIdentityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Identity/ConceptRelativeIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concept-relative identity is an equivalence relation and can identify strictly more "
            + "pairs than equality.",
        H("Concept-Relative Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("concept-relative-identity-is-an-equivalence-relation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "concept_identity_equivalence"),
                H("Concept-relative identity is an equivalence relation"),
                StatementSource.FromAuthor(EquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A concept readout partitions its source into fibers of equal observed value. "
                        + "Belonging to the same fiber is reflexive, symmetric, and transitive, so "
                        + "it defines an equivalence relation on the source objects."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("concept-relative-identity-can-be-strictly-coarser-than-equality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "concept_identity_strictly_coarser_than_equality"),
                H("Concept-relative identity can be strictly coarser than equality"),
                StatementSource.FromAuthor(StrictlyCoarserFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Literal equality is always preserved by every concept readout: equal "
                            + "objects necessarily receive the same concept value.")),
                    Paragraph(Text(
                        "The containment can be strict. The constant readout from the two Boolean "
                            + "values to the one-point type identifies false and true relative to "
                            + "the concept even though the two source values remain unequal."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula ConceptIdentity(
        Formula readout,
        Formula left,
        Formula right) =>
        Call("ConceptIdentity", readout, left, right);

    private static Formula EquivalenceFormula()
    {
        Formula source = F.Id("X");
        Formula concept = F.Id("C");
        Formula readout = F.Id("q");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("C", F.Id("Type")),
                Bound("q", Arrow(source, concept)),
            ],
            Call("Equivalence", Call("ConceptIdentity", readout))));
    }

    private static Formula StrictlyCoarserFormula()
    {
        Formula source = F.Id("X");
        Formula concept = F.Id("C");
        Formula readout = F.Id("q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula universalContainment = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("C", F.Id("Type")),
                Bound("q", Arrow(source, concept)),
                Bound("x", source),
                Bound("y", source),
            ],
            new Formula.Logic(
                Equal(left, right),
                FormulaLogicOperator.Implies,
                ConceptIdentity(readout, left, right)));

        Formula boolean = F.Id("Bool");
        Formula constantReadout = F.Id("q");
        Formula falseValue = F.Id("x");
        Formula trueValue = F.Id("y");
        Formula strictWitness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("q", Arrow(boolean, F.Id("Unit"))),
                Bound("x", boolean),
                Bound("y", boolean),
            ],
            new Formula.Logic(
                ConceptIdentity(constantReadout, falseValue, trueValue),
                FormulaLogicOperator.And,
                NotEqual(falseValue, trueValue)));

        return Disp(new Formula.Logic(
            universalContainment,
            FormulaLogicOperator.And,
            strictWitness));
    }
}
