using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class CarrylessSeventeenNineContainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/oeis2006a115809");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The seventeen-times binary carryless condition implies the nine-times condition.",
        H("Containment of Binary Carryless Multiplier Conditions"),
        Blocks(
            Paragraph(Text("Every variable ranges over the natural numbers, including zero. "
                + "C(u,k) is the natural number whose binary coefficients are the convolution "
                + "of the binary digits of u and k over GF(2), as in A048720. "
                + "All multiplication outside C is ordinary natural-number multiplication.")),
            Describe.Lean(DescribeId.Create("carryless-seventeen-nine-containment"),
                DeclarationHandle.Create(Prefix + "result"), H("The containment implication"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A state records the ordinary multiplication carry and "
                    + "the remaining exclusive-OR mask; a failed low-digit comparison gives a rejecting state. "
                    + "A relation with 101 paired states contains the initial pair and is closed "
                    + "under both binary input digits. At input zero, acceptance by the first state "
                    + "implies acceptance by the second. Binary induction transports this implication "
                    + "to every natural input. Thus the same k satisfying the condition defining "
                    + "A115809 also satisfies the condition defining A115801. No upper bound on k is imposed."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a115809-carryless-seventeen-nine-containment"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var k = F.Id("k");
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"), F.Id("Nat"), new Formula.Logic(
                Equal(Multiply(D(1, 7), k), Call("C", D(4, 9), k)),
                FormulaLogicOperator.Implies,
                Equal(Multiply(D(9), k), Call("C", D(2, 5), k)))));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [..args]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
