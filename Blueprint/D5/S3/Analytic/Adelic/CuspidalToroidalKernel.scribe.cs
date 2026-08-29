using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class CuspidalToroidalKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All normalized cuspidal quadratic-torus periods vanish exactly when the "
            + "base central value vanishes.",
        H("Cuspidal Toroidal Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cuspidal-all-torus-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/CuspidalToroidalKernel."
                        + "cuspidal_all_torus_kernel"),
                H("Cuspidal all-torus kernel equals the central-value kernel"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The normalized period, local factor, base central value, twisted "
                            + "central value, and adjoint denominator are exposed directly. "
                            + "Their norm-square relation is the displayed source identity.")),
                    Paragraph(Text(
                        "A zero base central value forces every period norm square to vanish. "
                            + "Conversely, the nonzero denominator and one nonzero local and "
                            + "twisted witness let cancellation recover the base value.")),
                    Paragraph(Text(
                        "Thus universal invisibility across the indexed quadratic-torus family "
                            + "is precisely the zero locus of the base central value."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("Index");
        Formula index = F.Id("i");
        Formula period = F.Id("P");
        Formula localFactor = F.Id("C");
        Formula twistedValue = F.Id("Ltwist");
        Formula centralValue = F.Id("Lcenter");
        Formula adjointValue = F.Id("Ladjoint");
        Formula realFamily = Arrow(indexType, real);
        Formula periodAtIndex = Apply(period, index);
        Formula localAtIndex = Apply(localFactor, index);
        Formula twistAtIndex = Apply(twistedValue, index);
        Formula numerator = Seq(
            localAtIndex, Sp, Times, Sp,
            Open, centralValue, Sp, Times, Sp, twistAtIndex, Close);

        Formula identity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            EqualTo(
                Call("normSq", periodAtIndex),
                new Formula.Fraction(numerator, adjointValue)));
        Formula adjointNonzero = NotEqualTo(adjointValue, D(0));
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("i", indexType)],
            And(
                NotEqualTo(localAtIndex, D(0)),
                NotEqualTo(twistAtIndex, D(0))));
        Formula invisible = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            EqualTo(periodAtIndex, D(0)));
        Formula criterion = new Formula.Logic(
            invisible,
            FormulaLogicOperator.Iff,
            EqualTo(centralValue, D(0)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("P", Arrow(indexType, complex)),
                Bound("C", realFamily),
                Bound("Ltwist", realFamily),
                Bound("Lcenter", real),
                Bound("Ladjoint", real),
            ],
            new Formula.Logic(
                And(identity, And(adjointNonzero, witness)),
                FormulaLogicOperator.Implies,
                criterion)));
    }
}
