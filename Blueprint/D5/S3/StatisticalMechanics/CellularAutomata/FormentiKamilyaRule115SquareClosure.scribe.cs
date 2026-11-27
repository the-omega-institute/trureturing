using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class FormentiKamilyaRule115SquareClosureDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.";
    private const string Rule =
        "D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/formentikamilya2026resoca115");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three is a least period of a finite RESOCA 115 configuration, and nine is impossible.",
        H("Question 2 for RESOCA 115 on the integer line"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("resoca115-square-closure-refuted"),
                DeclarationHandle.Create(Module + "result"),
                H("The realized least periods are not closed under squaring"),
                StatementSource.FromAuthor(SquareClosureRefuted()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Section 3, Question 2 on printed p. 97 asks “If p is a period for RESOCA 115, is p² also a period?” The update is the second-order rule from Equation (1) and Table 1. RealizesLeastPeriod(p) means that p is positive and some ordered pair of past and current Boolean layers on the integer line returns as a full pair after p steps, with no return at any positive q < p. The union of the two initial supports must be finite, as in Section 2.1. The two occurrences of RealizesLeastPeriod quantify their configurations independently.")),
                    Paragraph(Text("The all-zero pair has empty initial support. The theorem zero_period_three gives a return at three and excludes one and two. For any finite pair returning at nine, returns_three_of_returns_nine gives a return at three. Thus the implication in Question 2 fails at p = 3, since its consequent would require a pair with least period nine."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("formenti-kamilya-2026-resoca-115-question-2"),
                    ResolutionKind.Refuted))),
        [DocumentEdge.Dependency.Create(GidRef.Create(Rule))]));

    private static Formula SquareClosureRefuted()
    {
        Formula period = F.Id("p");
        Formula Realized(Formula value) =>
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("RealizesLeastPeriod"))), [value]);
        Formula square = Seq(period, Caret, Grp(D(2)));
        Formula implication = new Formula.Logic(
            Realized(period), FormulaLogicOperator.Implies, Realized(square));
        Formula closure = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("p"), Seq(Mathbb, Grp(F.Id("N"))), implication);
        return Disp(Seq(Neg, Sp, Open, closure, Close));
    }
}
