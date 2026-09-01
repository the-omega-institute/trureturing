using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Szego;

internal sealed class CanonicalTransferDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Szego/CanonicalTransfer.canonical_szego_su11_transfer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized Szego transfer matrix has the canonical determinant and "
            + "preserves the Hermitian form of signature (1,1).",
        H("Canonical Szego SU(1,1) Transfer Matrix"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-szego-su11-transfer"),
            DeclarationHandle.Create(Declaration),
            H("The canonical Szego transfer is normalized special unitary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The Verblunsky coefficient is required to lie in the open unit disk. "
                        + "This makes rho(alpha) positive and proves directly that the "
                        + "unnormalized-phase transfer has determinant z.")),
                Paragraph(Text(
                    "A point w on the unit circle with w squared equal to z records the "
                        + "chosen phase square root. The normalized matrix has determinant "
                        + "one and its conjugate transpose preserves diag(1,-1).")),
                Paragraph(Text(
                    "The module also verifies the alpha=0 diagonal case and the explicit "
                        + "alpha=1/2, z=2 matrix with rho=sqrt(3)/2 and determinant two. "
                        + "No Li-Clark uniqueness or hyperbolicity claim is asserted."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula circle = Raised(F.Id("S"), D(1));
        Formula alpha = F.Id("alpha");
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        Formula premise = And(
            Less(Call("norm", alpha), D(1)),
            Equal(Raised(w, D(2)), z));
        Formula conclusion = And(
            Less(D(0), Call("rho", alpha)),
            And(
                Equal(Call("det", Call("A", alpha, z)), z),
                Call("IsSpecialUnitary11", Call("normalizedA", alpha, w))));

        return Disp(ForAll(
            [Bound("alpha", complex), Bound("z", complex), Bound("w", circle)],
            Implies(premise, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Raised(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
