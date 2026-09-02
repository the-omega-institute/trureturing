using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class JetPencilFiniteExpansionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite nilpotent jet pencil has an explicit determinant and inverse series.",
        H("Jet Pencil Finite Expansion"),
        Blocks(Describe.Lean(
            DescribeId.Create("jet-pencil-finite-expansion"),
            DeclarationHandle.Create(
                "D5/S3/Observer/BlockStructure/JetPencilFiniteExpansion."
                    + "jet_pencil_finite_expansion"),
            H("The nilpotent pencil terminates after its jet length"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a natural length m, nilpotentJetShift m is the matrix with a one "
                        + "exactly one step below the diagonal and zero elsewhere. The reused "
                        + "jetPencil m rho s is (s-rho) times the identity minus this shift.")),
                Paragraph(Text(
                    "The sole premise s != rho is the exact nonvanishing condition for the "
                        + "displayed inverse. It makes the determinant a unit and prevents "
                        + "totalized scalar division from disguising the singular spectral "
                        + "point. No positivity assumption on m is needed; at m = 0 the empty "
                        + "matrix identities remain valid.")),
                Paragraph(Text(
                    "Lower triangularity gives determinant (s-rho)^m. Cayley-Hamilton makes "
                        + "the m-th shift power zero, so the geometric inverse terminates at "
                        + "k = m-1. Nilpotence of every positive power and the pinned matrix "
                        + "trace lemma give trace zero for every k >= 1. Lean represents each "
                        + "matrix quotient by inverse scalar multiplication."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula length = F.Id("m");
        Formula rho = F.Id("rho");
        Formula point = F.Id("s");
        Formula index = F.Id("k");
        Formula difference = Seq(point, Sp, Minus, Sp, rho);
        Formula shift = Call("nilpotentJetShift", length);
        Formula pencil = Call("jetPencil", length, rho, point);
        Formula determinant = Call("det", pencil);
        Formula determinantClause = EqualTo(
            determinant,
            Power(Grp(difference), length));
        Formula unitClause = Call("IsUnit", determinant);
        Formula summand = new Formula.Fraction(
            Power(shift, index),
            Power(Grp(difference), Seq(index, Sp, Plus, Sp, D(1))));
        Formula finiteSeries = Seq(
            Sum, Underscore, Grp(Seq(index, Eq, D(0))), Caret,
            Grp(Seq(length, Sp, Minus, Sp, D(1))), Sp, summand);
        Formula inverseClause = EqualTo(
            Power(pencil, Seq(Minus, D(1))),
            finiteSeries);
        Formula traceClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("k", natural)],
            Implies(
                LessThanOrEqual(D(1), index),
                EqualTo(Call("trace", Power(shift, index)), D(0))));
        Formula conclusion = And(
            determinantClause,
            And(unitClause, And(inverseClause, traceClause)));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("m", natural),
                Bound("rho", complex),
                Bound("s", complex),
            ],
            Implies(NotEqualTo(point, rho), conclusion));
    }
}
