using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.IcosahedralGeometry;

internal sealed class ProjectiveAxisDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite icosahedral action partitions the projective plane over F5 "
            + "into its three axis orbits.",
        H("Finite Icosahedral Axis Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-icosahedral-axis-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecomposition."
                        + "finite_icosahedral_axis_decomposition"),
                H("The projective axes split into the fivefold, threefold, and twofold orbits"),
                StatementSource.FromAuthor(ProjectiveAxisDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is Mathlib's projectivization of the three-dimensional "
                            + "vector space over F5. Its cardinality 31 is derived from the "
                            + "projectivization cardinality theorem, and a proved equivalence to "
                            + "the 31-entry coordinate chart transports the finite computation.")),
                    Paragraph(Text(
                        "The source quadratic form defines three concrete classes in the actual "
                            + "projective plane. They are pairwise disjoint, their union is the "
                            + "whole projective plane, and their cardinalities are 6, 10, and 15.")),
                    Paragraph(Text(
                        "The two source matrices define a linear A5 action, and Mathlib induces "
                            + "its action on projectivization. The coordinate equivalence is proved "
                            + "equivariant for this action; every class is one orbit, with "
                            + "stabilizer cardinalities 10, 6, and 4.")),
                    Paragraph(Text(
                        "For every fivefold axis, the subgroup of stabilizing rotations whose "
                            + "fifth power is the identity has cardinality 5 and is cyclic. The "
                            + "axis stabilizer is exactly the normalizer of this subgroup."))),
                DescribeRole.Theorem))));

    private static Formula ProjectiveAxisDecompositionFormula()
    {
        Formula a5 = Seq(Mathcal, Grp(F.Id("A")), Underscore, Grp(D(5)));
        Formula a3 = Seq(Mathcal, Grp(F.Id("A")), Underscore, Grp(D(3)));
        Formula a2 = Seq(Mathcal, Grp(F.Id("A")), Underscore, Grp(D(2)));
        Formula p = F.Id("p");
        Formula projectivePlane = Seq(
            Mathbb, Grp(F.Id("P")), Caret, Grp(D(2)),
            Open, Mathbb, Grp(F.Id("F")), Underscore, Grp(D(5)), Close);

        Formula Card(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
        Formula Orbit(Formula value) => Call("orbit", value);
        Formula Stabilizer(Formula value) => Call("Stab", value);
        Formula FiveCycle(Formula value) => Call("C5", value);
        Formula ForEvery(Formula axes, Formula body) => Seq(
            Open, Forall, Sp, p, Sp, InMacro, Sp, axes, Comma, Esc, body, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Call("Disjoint", a5, a3), Sp, Land, Sp,
            Call("Disjoint", a5, a2), Sp, Land, Sp,
            Call("Disjoint", a3, a2), Sp, Land, RowBreak, Grp(),
            Call("union", a5, a3, a2), Sp, Eq, Sp, projectivePlane,
            Sp, Land, RowBreak, Grp(),
            Card(a5), Sp, Eq, Sp, D(6), Sp, Land, Sp,
            Card(a3), Sp, Eq, Sp, D(1, 0), Sp, Land, Sp,
            Card(a2), Sp, Eq, Sp, D(1, 5), Sp, Land, RowBreak, Grp(),
            ForEvery(a5, Seq(Orbit(p), Sp, Eq, Sp, a5)), Sp, Land, RowBreak, Grp(),
            ForEvery(a3, Seq(Orbit(p), Sp, Eq, Sp, a3)), Sp, Land, RowBreak, Grp(),
            ForEvery(a2, Seq(Orbit(p), Sp, Eq, Sp, a2)), Sp, Land, RowBreak, Grp(),
            ForEvery(a5, Seq(Card(Stabilizer(p)), Sp, Eq, Sp, D(1, 0))),
            Sp, Land, RowBreak, Grp(),
            ForEvery(a3, Seq(Card(Stabilizer(p)), Sp, Eq, Sp, D(6))),
            Sp, Land, RowBreak, Grp(),
            ForEvery(a2, Seq(Card(Stabilizer(p)), Sp, Eq, Sp, D(4))),
            Sp, Land, RowBreak, Grp(),
            ForEvery(a5, Seq(
                Card(FiveCycle(p)), Sp, Eq, Sp, D(5), Sp, Land, Sp,
                Call("Cyclic", FiveCycle(p)), Sp, Land, Sp,
                Stabilizer(p), Sp, Eq, Sp, Call("Normalizer", FiveCycle(p)))), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
