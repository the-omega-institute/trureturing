using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class SilverSlopeAbelianPeriodsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/peltomaki2020abelianperiods");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The silver-slope abelian-period conjecture.",
        H("Silver-Slope Abelian Periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("silver-slope-conjecture"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.claim"),
                H("Peltomäki's silver-slope conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    SourceQuotation(),
                    Paragraph(Text(
                        "The displayed equality encodes that sentence with the literal period-set and "
                            + "candidate-set definitions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("silver-slope-result"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.result"),
                H("The silver-slope period set equality"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(Call("silverAbelianPeriodSet"),FormulaRelationOperator.Equal,Call("silverCandidateSet")))),
                AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(
                    "Every Pell denominator, twice a denominator and positive adjacent-denominator sum is realised. Singular-window packing excludes all other minimum periods."))),DescribeRole.Theorem)),
        []));

    private static DocumentBlock SourceQuotation() => Paragraph(
        Text("Verbatim source sentence (p. 283, line 1722): Let "),
        Math(Seq(Alpha, Sp, Eq, Sp, OpenBracket, D(0), Semi, Sp, Overline, Grp(D(2)), CloseBracket)),
        Text(". The abelian period set of a Sturmian word of slope "), Math(Alpha), Text(" is "),
        Math(Seq(Mathcal, Grp(F.Id("Q")), Caret, Grp(Plus), Underscore, Grp(Alpha), Sp, Cup, Sp,
            Mathcal, Grp(F.Id("M")), Underscore, Grp(Alpha))), Text("."));


    private static Formula ClaimFormula() => Disp(new Formula.Logic(Call("claim"),FormulaLogicOperator.Iff,
        new Formula.Relation(Call("silverAbelianPeriodSet"),FormulaRelationOperator.Equal,Call("silverCandidateSet"))));
    private static Formula Call(string name) => Seq(Operatorname,Grp(F.Id(name)),Parenthesized(Seq()));
    private static Formula Parenthesized(Formula f) => Seq(Open,f,Close);}
