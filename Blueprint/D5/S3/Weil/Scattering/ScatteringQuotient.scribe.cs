using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class ScatteringQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var half = new Formula.Fraction(Num(1), Num(2));
        var t = F.Id("t");
        var imaginary = F.Id("i");
        var reflected = Call(
            "completedZetaReading",
            Subtract(half, Multiply(t, imaginary)));
        var direct = Call(
            "completedZetaReading",
            Add(half, Multiply(t, imaginary)));
        var quotientNorm = new Formula.Norm(new Formula.Fraction(reflected, direct));
        var statement = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("t"),
            Grp(Mathbb, Grp(F.Id("R"))),
            new Formula.Logic(
                NotEqual(direct, Num(0)),
                FormulaLogicOperator.Implies,
                Equal(quotientNorm, Num(1))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A real spectral parameter gives a unit-modulus quotient of the completed zeta reading.",
            H("Real Spectral Scattering Quotient"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("real-spectral-scattering-quotient-norm"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/Scattering/ScatteringQuotient.real_spectral_scattering_quotient_norm"),
                    H("Real spectral scattering quotient has unit norm"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "This is the leading unitary clause of the source scattering form. "
                            + "For a real spectral parameter, the reflected completed-zeta values "
                            + "coincide by the functional equation, so their quotient has norm one "
                            + "when the denominator is nonzero.")),
                        Paragraph(Text(
                            "The declaration is an honest partial closure. It does not define a "
                            + "scattering matrix, phase branch, zero-counting function, phase jumps, "
                            + "Wigner delay, numerical certificate, or physical interpretation; "
                            + "all of those source clauses remain unresolved."))),
                    DescribeRole.Theorem)),
            []));
    }
}
