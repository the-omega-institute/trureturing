using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class FiniteDistanceInvariantSectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite observer distance forces equal evaluation on every bounded invariant observable.",
        H("Finite-Distance Invariant Sectors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-distance-points-share-an-invariant-sector"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/FiniteDistanceInvariantSector."
                        + "finite_distance_same_invariant_sector"),
                H("Finite-distance points share an invariant sector"),
                StatementSource.FromAuthor(FiniteDistanceInvariantSectorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let tau be a permutation and let x and y have finite extended observer "
                            + "distance. Then every bounded complex observable with zero update "
                            + "defect takes the same value at x and y.")),
                    Paragraph(Text(
                        "If such an observable separated the points, the frozen invariant-separation "
                            + "theorem would force their observer distance to be infinity, contrary "
                            + "to finiteness. Equality on every invariant observable is precisely the "
                            + "fiber condition for the restriction-by-evaluation map.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no existing finite-distance "
                            + "fiber theorem. The proof imports and directly applies the repository's "
                            + "general invariant-separation theorem by contrapositive. Loogle found "
                            + "no exact upstream match."))),
                DescribeRole.Theorem))));

    private static Formula FiniteDistanceInvariantSectorFormula()
    {
        Formula carrier = F.Id("I");
        Formula update = Tau;
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula observable = F.Id("f");
        Formula distance = Seq(
            F.Id("d"), Underscore, update, Open, x, Comma, Sp, y, Close);
        Formula defect = Seq(
            F.Id("L"), Underscore, update, Open, observable, Close);

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            update, Colon, Sp, Operatorname, Grp(F.Id("Perm")), Open, carrier, Close,
            Comma, Sp, x, Comma, Sp, y, Colon, Sp, carrier, Comma, Esc,
            distance, Sp, Neq, Sp, Infty, Sp, Rightarrow, Sp,
            Forall, Sp, observable, Colon, Sp, carrier, Sp, To, Sp,
            Operatorname, Grp(F.Id("Complex")), Comma, Esc,
            Operatorname, Grp(F.Id("Bounded")), Open, observable, Close,
            Sp, Rightarrow, Sp,
            defect, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            observable, Open, x, Close, Sp, Eq, Sp,
            observable, Open, y, Close, Dot));
    }
}
