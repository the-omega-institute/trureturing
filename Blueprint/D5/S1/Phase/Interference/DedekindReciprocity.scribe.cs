using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class DedekindReciprocityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dedekind reciprocity follows from exact finite residue sums and a coprime lattice-point exchange.",
        H("Dedekind Reciprocity by Finite Sums"),
        Blocks(
            Paragraph(Text(
                "The proof uses only exact rational arithmetic. It rewrites the frozen phase-1 "
                    + "sawtooth through reduced residues, evaluates the linear and square residue "
                    + "sums, converts the cross term by Euclidean division, and double-counts the "
                    + "two strict triangles in a coprime lattice rectangle.")),
            Describe.Lean(
                DescribeId.Create("dedekind-reciprocity"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindReciprocity.dedekind_reciprocity"),
                H("Dedekind reciprocity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), Comma, Sp, F.Id("d"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("c"), Gt, D(0), Sp, Land, Sp,
                    F.Id("d"), Gt, D(0), Sp, Land, Sp,
                    Gcd, Open, F.Id("c"), Comma, Sp, F.Id("d"), Close,
                    Eq, D(1), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    F.Id("d"), Comma, Sp, F.Id("c"), Close,
                    Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    F.Id("c"), Comma, Sp, F.Id("d"), Close,
                    Sp, Eq, Sp,
                    Minus, Frac, Grp(D(1)), Grp(D(4)), Sp, Plus, Sp,
                    Frac,
                    Grp(
                        Frac, Grp(F.Id("c")), Grp(F.Id("d")),
                        Sp, Plus, Sp,
                        Frac, Grp(F.Id("d")), Grp(F.Id("c")),
                        Sp, Plus, Sp,
                        Frac, Grp(D(1)),
                            Grp(F.Id("c"), F.Id("d"))),
                    Grp(D(1, 2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The named ladder is sawtooth_div_eq_mod and dedekindSum_eq_mod_sum; "
                            + "sum_Ico_cast, sum_Ico_cast_sq, and sum_mul_mod; sum_div_gauss, "
                            + "latticeDifference_closed, and weightedFloorSum_exchange; followed "
                            + "by dedekindSum_eq_residueCrossTerm and the final rational assembly.")),
                    Paragraph(Text(
                        "Coprimality is used to permute the nonzero residues and to exclude diagonal "
                            + "points from the lattice rectangle. No analytic convergence or "
                            + "continued-fraction induction enters this theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dedekind-reciprocity-three-four"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindReciprocity."
                    + "dedekind_reciprocity_three_four"),
                H("The exact three-four reciprocity check"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    D(3), Comma, Sp, D(4), Close,
                    Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("dedekindSum")), Open,
                    D(4), Comma, Sp, D(3), Close,
                    Sp, Eq, Sp, Minus, Frac, Grp(D(5)), Grp(D(7, 2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the coprime pair three and four, the two exact rational sums total "
                        + "minus five seventy-seconds; together with the frozen value "
                        + "dedekindSum(3,4) = -1/8, this gives dedekindSum(4,3) = 1/18."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/Interference/DedekindBhkCertificates")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/Interference/DedekindReciprocityFiniteSums")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/Interference/DedekindReciprocityLattice")),
        ]));
}
