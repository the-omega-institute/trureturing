using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class CarrylessThirteenElevenContainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/oeis2026a115803");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The carryless-multiplier equation for 13 and 29 implies the equation for 11 and 31.",
        H("A115805 to A115803 carryless containment"),
        Blocks(
            Paragraph(Text("Every variable ranges over the natural numbers, including zero. "
                + "Ordinary multiplication and binary carryless multiplication are different operations. "
                + "The carryless product C uses binary digits as polynomial coefficients over GF(2).")),
            Describe.Lean(DescribeId.Create("carryless-thirteen-eleven-containment"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Containment of the solution sets"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A finite relation of 50 state pairs has the required terminal implication "
                    + "and is closed under both input digits. The original binary-product recursion and "
                    + "its holds_step theorem turn this finite certificate into an induction over every "
                    + "natural number. The certificate is a proof component; its bounded enumeration is "
                    + "not used as a substitute for the all-natural-number induction."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a115803-carryless-thirteen-eleven-containment"),
                    ResolutionKind.Proved))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence"))]));

    private static Formula ResultFormula()
    {
        var k = F.Id("k");
        var premise = Equal(Multiply(D(1, 3), k), Call("C", D(2, 9), k));
        var conclusion = Equal(Multiply(D(1, 1), k), Call("C", D(3, 1), k));
        return Disp(Universal("k", new Formula.Logic(
            premise, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [..args]);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Multiply(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Universal(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), F.Id("Nat"), body);
}
