using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class DedekindReciprocityLatticeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite coprime lattice double count evaluates the symmetric weighted floor sum.",
        H("The Weighted Lattice Exchange"),
        Blocks(
            Paragraph(Text(
                "Rows below the strict diagonal are finite intervals determined by Euclidean "
                    + "division. Coprimality excludes diagonal points, so the two strict triangles "
                    + "partition the complete residue rectangle.")),
            Describe.Lean(
                DescribeId.Create("weighted-floor-sum-exchange"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindReciprocityLattice."
                    + "weightedFloorSum_exchange"),
                H("The symmetric weighted floor exchange"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, Sp, F.Id("c"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("c"), Gt, D(0), Sp, Land, Sp,
                    F.Id("d"), Gt, D(0), Sp, Land, Sp,
                    Gcd, Open, F.Id("c"), Comma, Sp, F.Id("d"), Close,
                    Eq, D(1), Sp, Rightarrow, Sp,
                    F.Id("d"), Operatorname, Grp(F.Id("weightedFloorSum")), Open,
                    F.Id("d"), Comma, Sp, F.Id("c"), Close,
                    Sp, Plus, Sp,
                    F.Id("c"), Operatorname, Grp(F.Id("weightedFloorSum")), Open,
                    F.Id("c"), Comma, Sp, F.Id("d"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("latticeDifference")), Open,
                    F.Id("d"), Comma, Sp, F.Id("c"), Close,
                    Sp, Plus, Sp,
                    Frac,
                    Grp(F.Id("c"), Open, F.Id("c"), Minus, D(1), Close,
                        F.Id("d"), Open, F.Id("d"), Minus, D(1), Close),
                    Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same module proves the unweighted Gauss floor count, evaluates the "
                        + "positive lattice difference row by row, and separates the two coordinate "
                        + "weights before this symmetric assembly."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/Interference/DedekindReciprocityFiniteSums")),
        ]));
}
