using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Representation;

internal sealed class UnitJordanRepresentationSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Representation/UnitJordanRepresentationSeparation."
            + "unit_jordan_representation_separation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The identity and unit-Jordan generator actions have distinct minimal polynomials "
            + "but the same two trivial graded factors.",
        H("Unit-Jordan Representation Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("unit-jordan-representations-separate-before-semisimplification"),
            DeclarationHandle.Create(Declaration),
            H("The representations differ while their graded factors agree"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary field K, the identity generator is the identity linear "
                        + "endomorphism of K times K. The unipotent generator is constructed "
                        + "from the canonical unit-Jordan action (x,y) maps to (x+y,y).")),
                Paragraph(Text(
                    "The nilpotent part is the difference between those generator actions. "
                        + "It is nonzero, its square vanishes, and linear independence of the "
                        + "identity and the unipotent action gives the exact quadratic minimal "
                        + "polynomial.")),
                Paragraph(Text(
                    "Here gr(T) is the action on the direct sum of the invariant first-axis "
                        + "factor and the quotient read by the second coordinate: its value at "
                        + "(x,y) is ((T(x,0)).first,(T(0,y)).second). Both displayed graded "
                        + "actions are therefore the direct sum of two trivial factors.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies the generic minimal-polynomial uniqueness result. "
                        + "Repository search found the canonical Jordan action but no theorem "
                        + "combining minimal polynomials, non-conjugacy, and graded factors."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula field = F.Id("K");
        Formula identity = new Formula.Subscript(F.Id("I"), field);
        Formula jordan = new Formula.Subscript(F.Id("U"), field);
        Formula nilpart = new Formula.Subscript(F.Id("N"), field);
        Formula variable = F.Id("t");
        Formula linearEquivalence = F.Id("e");
        Formula two = D(2);
        Formula tMinusOne = Seq(variable, Sp, Minus, Sp, D(1));
        Formula squaredTMinusOne = Seq(Grp(tMinusOne), Caret, Grp(two));
        Formula squaredNilpart = Seq(nilpart, Caret, Grp(two));
        Formula carrier = Seq(field, Caret, Grp(two));
        Formula intertwining = Equal(
            Seq(linearEquivalence, Sp, Circ, Sp, identity),
            Seq(jordan, Sp, Circ, Sp, linearEquivalence));
        Formula noIntertwiner = new Formula.Not(new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("e"),
            Call("LinearEquiv", field, carrier, carrier),
            intertwining));
        Formula noRepresentationEquivalence = new Formula.Not(Call(
            "RepresentationEquiv",
            Call("trivialRepresentation", field, Call("Multiplicative", F.Id("Z")), carrier),
            Call("unitJordanRepresentation", field)));
        Formula conclusions = And(
            Equal(Call("minpoly", field, identity), tMinusOne),
            And(
                new Formula.Not(Equal(nilpart, D(0))),
                And(
                    Equal(squaredNilpart, D(0)),
                    And(
                        Equal(Call("minpoly", field, jordan), squaredTMinusOne),
                        And(
                            noIntertwiner,
                            And(
                                noRepresentationEquivalence,
                                And(
                                    Equal(Call("gr", identity), identity),
                                    Equal(Call("gr", jordan), identity))))))));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, field, Comma, Sp, Call("Field", field), Sp, Rightarrow),
            Seq(
                identity, Sp, Eq, Sp, Call("identityEnd", carrier), Comma, Sp,
                jordan, Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                Sp, Eq, Sp, Open, F.Id("x"), Sp, Plus, Sp, F.Id("y"),
                Comma, Sp, F.Id("y"), Close, Comma),
            Seq(nilpart, Sp, Eq, Sp, jordan, Sp, Minus, Sp, identity, Comma),
            Seq(conclusions, Dot),
        ]));
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
