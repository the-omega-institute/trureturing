using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Composition;

internal sealed class ConnectionCoefficientCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var a = F.Id("a");
        var b = F.Id("b");
        var X = F.Id("X");
        var Y = F.Id("Y");
        var Z = F.Id("Z");
        var first = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("b"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("Z"), reals),
            ],
            new Formula.Logic(
                Equal(Y, Multiply(a, X)),
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    Equal(Z, Multiply(b, Y)),
                    FormulaLogicOperator.Implies,
                    Equal(Z, Multiply(Seq(Open, Multiply(a, b), Close), X)))));

        var x = F.Id("x");
        var radicand = new Formula.Fraction(
            Multiply(Pi, Call("exp", x)),
            Multiply(Num(2), x));
        var gaussian = new Formula.Fraction(Pi, Num(2));
        var exponential = new Formula.Fraction(x, Num(2));
        var scaleExponent = new Formula.Fraction(new Formula.Negate(Num(1)), Num(2));
        var second = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            reals,
            new Formula.Logic(
                new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, x),
                FormulaLogicOperator.Implies,
                Equal(
                    Call("sqrt", radicand),
                    Multiply(
                        Multiply(Call("sqrt", gaussian), Call("exp", exponential)),
                        new Formula.Power(x, scaleExponent)))));

        var statement = new Formula.Logic(first, FormulaLogicOperator.And, second);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Connection coefficients multiply along a two-step completion path, with the Ramanujan 541 radical split into Gaussian, exponential, and scale factors.",
            H("Connection Coefficient Multiplication"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("connection-coefficient-multiplication"),
                    DeclarationHandle.Create(
                        "D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication"),
                    H("Connection coefficients multiply along completion paths"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The first conjunct formalizes the two-step scalar path: if Y is aX and Z is bY, then Z is (ab)X. The real field supplies the commutative rearrangement used by the Lean proof.")),
                        Paragraph(Text(
                            "The second conjunct records the Ramanujan 541 factorization on the positive real domain. It separates the Gaussian total mass, exponential flow, and scale Jacobian exactly as displayed in the source.")),
                        Paragraph(Text(
                            "The first conjunct is discharged by elementary ring normalization. The second is assembled from pinned Mathlib square-root, exponential, and real-power identities; no unproved hypothesis or replacement object is introduced."))),
                    DescribeRole.Theorem)),
            []));
    }
}
