using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class FiniteSubspaceComplementAbsorptionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/FiniteSubspaceComplementAbsorption."
            + "finite_subspace_complement_absorption";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing a finite-dimensional subspace preserves the Hilbert dimension and unitary "
            + "type of an infinite-dimensional Hilbert space.",
        H("Finite Subspace Complement Absorption"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-subspace-complement-absorption"),
                DeclarationHandle.Create(Declaration),
                H("A finite extraction leaves a full-dimensional complement"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A common index type carries an explicit Hilbert basis of the "
                            + "orthogonal complement and an explicit Hilbert basis of the "
                            + "ambient space, which states equality of Hilbert dimension.")),
                    Paragraph(Text(
                        "The complement unitary is the composition of the two basis "
                            + "representations. The quotient unitary then composes the canonical "
                            + "quotient-to-orthogonal-complement isometry with that unitary.")),
                    Paragraph(Text(
                        "The proof extends a finite orthonormal basis of the extracted subspace "
                            + "to an ambient Hilbert basis. It applies the frozen basis-tail "
                            + "construction to the remaining coordinates and uses finite-cardinal "
                            + "absorption only to reindex that tail."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula subspace = F.Id("M");
        Formula index = F.Id("I");
        Formula complementBasis = F.Id("bperp");
        Formula ambientBasis = F.Id("b");
        Formula complementUnitary = F.Id("U");
        Formula quotientUnitary = F.Id("Q");

        Formula submodule = Call("Submodule", scalar, space);
        Formula complement = Call("orthogonalComplement", subspace);
        Formula quotient = Call("SubmoduleQuotient", space, subspace);
        Formula complementBasisType = Call("HilbertBasis", index, scalar, complement);
        Formula ambientBasisType = Call("HilbertBasis", index, scalar, space);
        Formula ComplementUnitaryType() =>
            Call("LinearIsometryEquiv", scalar, complement, space);
        Formula QuotientUnitaryType() =>
            Call("LinearIsometryEquiv", scalar, quotient, space);

        Formula hypotheses = And(
            Call("RCLike", scalar),
            And(
                Call("NormedAddCommGroup", space),
                And(
                    Call("InnerProductSpace", scalar, space),
                    And(
                        Call("CompleteSpace", space),
                        And(
                            Call("FiniteDimensional", scalar, subspace),
                            new Formula.Not(Call(
                                "FiniteDimensional", scalar, space)))))));

        Formula basisComposition = Call(
            "trans",
            Call("repr", complementBasis),
            Call("symm", Call("repr", ambientBasis)));
        Formula quotientComposition = Call(
            "trans",
            Call("quotientEquivOrthogonal", subspace),
            complementUnitary);
        Formula computationRules = And(
            Equal(complementUnitary, basisComposition),
            Equal(quotientUnitary, quotientComposition));

        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("I", type)],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("bperp", complementBasisType)],
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("b", ambientBasisType)],
                    new Formula.BindMany(
                        FormulaQuantifier.Exists,
                        [Bound("U", ComplementUnitaryType())],
                        new Formula.BindMany(
                            FormulaQuantifier.Exists,
                            [Bound("Q", QuotientUnitaryType())],
                            computationRules)))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("K", type),
                Bound("H", type),
                Bound("M", submodule),
            ],
            new Formula.Logic(
                hypotheses,
                FormulaLogicOperator.Implies,
                conclusion)));
    }
}
