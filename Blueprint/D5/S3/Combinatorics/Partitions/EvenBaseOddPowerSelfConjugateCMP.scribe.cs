using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class EvenBaseOddPowerSelfConjugateCMPDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/dietzflowerslockard2026cmp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least odd exponent admitting a self-conjugate CMP at an even base, as asked in Question 5.12 of Dietz, Flowers and Lockard.",
        H("The least odd exponent for a self-conjugate CMP at an even base"),
        Blocks(Describe.Lean(
            DescribeId.Create("dfl512-diagram"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.publishedDiagram"),
            H("The published diagram"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("publishedDiagram"), Colon, Naturals, To, Named("YoungDiagram")))),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("For each j from zero through m, take the rectangle with height m to the power j and width m to the power m − j, with its upper left cell at the origin. The diagram is the union of these rectangles. Its row lengths and multiplicities are those of Flowers and Lockard, Lemma 4.2."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("dfl512-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.result"),
            H("Minimum odd exponent"),
            StatementSource.FromAuthor(Disp(Minimum())),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Write N for the number of cells and L for the first row length. The first row and column meet in one cell, and the diagram lies inside an L by L square. Thus 2L − 1 ≤ N ≤ L². If N = mᵉ and L = mᴷ, with e odd, these bounds give 0 < 2K − e ≤ e − 2. The square congruence for N − (2L − 1), together with the first-order expansion of the two powers modulo (m − 1)², shows that m − 1 divides 2K − e. Hence e ≥ m + 1, including at base 2 and for the candidate e = 1.")),
                Paragraph(Text("The attaining diagram is the union of rectangles with height mʲ and width m to the power m − j, for j = 0 through m. Transposition swaps the rectangles indexed by j and m − j. The top row has width mᵐ. For each j from 1 through m, the rows with zero-based index from m to the power j − 1 inclusive up to mʲ exclusive have width m to the power m − j. These are the multiplicities in Flowers and Lockard, Lemma 4.2, cited in Discussion 5.11 of the source. Each of those m bands has mᵐ − m to the power m − 1 cells, so the exact area is m to the power m + 1. Evenness of m makes that exponent odd."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("dfl512-even-odd-power"),
                ResolutionKind.Proved))), []));

    private static Formula Minimum()
    {
        Formula m = F.Id("m"), e = F.Id("e"), mu = F.Id("mu");
        Formula naturals = Naturals;
        Formula diagram = And(Equal(Call("card", mu), new Formula.Power(m, e)),
            And(Call("IsCMP", m, mu), Equal(Call("transpose", mu), mu)));
        Formula eligible = And(Call("Odd", e),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("mu"),
                Named("YoungDiagram"), Par(diagram)));
        Formula exponents = Seq(OpenBrace, new Formula.Relation(e, FormulaRelationOperator.MemberOf, naturals), Mid, eligible, CloseBrace);
        Formula minimum = Call("IsLeast", exponents,
            new Formula.Binary(m, FormulaBinaryOperator.Add, new Formula.Number(1)));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("m"), naturals,
            Par(Imp(new Formula.Relation(new Formula.Number(2), FormulaRelationOperator.LessThanOrEqual, m),
                Imp(Call("Even", m), minimum))));
    }

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
}
