using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class GreathouseLogTwoFloorRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/GreathouseLogTwoFloorRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/greathouse2012a175406");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The OEIS A175406 floor formula is refuted at a large explicit index.",
        H("The OEIS A175406 Greathouse Floor Formula"),
        Blocks(
            Describe.Lean(DescribeId.Create("a175406-sequence-value"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The sequence value"),
                StatementSource.FromAuthor(AFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural n, including zero, a(n) takes the natural sSup "
                        + "of exponents k satisfying the displayed bound. Powers and "
                        + "division are real, with Lean's 1/0 = 0 convention. Natural "
                        + "sSup is 0 for unbounded sets, so a is total."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a175406-floor-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Greathouse's floor conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every positive natural n, the conjecture identifies a(n) "
                        + "with the displayed natural floor. The subscript plus denotes "
                        + "Nat.floor, and log is the natural logarithm."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a175406-floor-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The floor conjecture is false"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At n0 = 1121626023352383, let M = 777451915729368. The certified "
                        + "log-series estimates give the stated natural floor as M, while "
                        + "the defining supremum is M - 1: the M-th power is greater than 2 "
                        + "and the (M - 1)-st power is at most 2. The proof uses 36 positive "
                        + "terms and a geometric tail for log 2, two positive terms for the "
                        + "witness logarithm, and log(1+x) <= x. No minimality claim is made."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a175406-log-two-floor-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var baseValue = Seq(Open, D(1), Plus, D(1), Slash, n, Close);
        // Escaped spaces preserve row breaks through Markdown parsing.
        return Disp(Seq(Nl, Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, InMacro, Naturals(), Comma, RowBreak, Esc, Grp(),
            F.Id("a"), Open, n, Close, Eq, Mathrm, Grp(F.Id("sSup")),
            Begin, Grp(F.Id("Bmatrix")),
            k, InMacro, Naturals(), Mid, Sp,
            new Formula.Power(baseValue, k), Leq, D(2),
            End, Grp(F.Id("Bmatrix")), End, Grp(F.Id("gathered")), Nl));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        return Disp(Seq(Nl, Begin, Grp(F.Id("gathered")),
            Mathrm, Grp(F.Id("claim")), Leftrightarrow, RowBreak, Esc, Grp(),
            Forall, Sp, n, InMacro, Naturals(), Comma, Esc,
            n, Geq, D(1), Rightarrow, RowBreak, Esc, Grp(),
            F.Id("a"), Open, n, Close, Eq,
            Lfloor, Open, n, Plus, D(1), Slash, D(2), Close,
            Log, Sp, D(2), Rfloor, Underscore, Plus,
            End, Grp(F.Id("gathered")), Nl));
    }

    private static Formula ResultFormula() =>
        Disp(Seq(Nl, Neg, Mathrm, Grp(F.Id("claim")), Nl));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));
}
