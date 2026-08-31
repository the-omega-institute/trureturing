using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class IcosahedralAxisDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 31 points of P2(F5) split into the 6, 10, and 15 icosahedral axis classes.",
        H("Finite Icosahedral Axis Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-projective-plane-cardinality"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/IcosahedralAxisDecomposition."
                        + "finite_projective_plane_cardinality"),
                H("The finite projective plane has 31 points"),
                StatementSource.FromAuthor(ProjectivePlaneCardinality()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normalized representatives are proved equivalent to Mathlib's quotient "
                        + "projectivization. Both presentations therefore have 31 points."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("finite-projective-axis-partition"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/IcosahedralAxisDecomposition."
                        + "finite_projective_axis_partition"),
                H("The three quadratic classes form a disjoint partition"),
                StatementSource.FromAuthor(ProjectivePartition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero, nonsquare, and square quadratic-value classes cover every "
                        + "projective point and are pairwise disjoint."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("finite-projective-axis-cardinalities"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/IcosahedralAxisDecomposition."
                        + "finite_projective_axis_cardinalities"),
                H("The three projective classes have sizes 6, 10, and 15"),
                StatementSource.FromAuthor(ProjectiveClassCardinalities()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exact finite evaluation of the displayed quadratic matrix gives six "
                        + "isotropic, ten nonsquare, and fifteen square directions."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("icosahedral-axis-orbits"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/IcosahedralAxisDecomposition.icosahedral_axis_orbits"),
                H("The cyclic axes form three conjugacy orbits"),
                StatementSource.FromAuthor(AxisOrbitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Canonical cyclic generators in A5 give single conjugacy classes at "
                        + "orders five, three, and two, with sizes six, ten, and fifteen."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("icosahedral-axis-stabilizer-orders"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/IcosahedralAxisDecomposition."
                        + "icosahedral_axis_stabilizer_orders"),
                H("The axis stabilizers have orders 10, 6, and 4"),
                StatementSource.FromAuthor(AxisStabilizerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cyclic-axis normalizers have the stated orders. For every twofold "
                        + "axis, its normalizer equals the generator centralizer."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("finite-icosahedral-axis-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/IcosahedralAxisDecomposition."
                        + "finite_icosahedral_axis_decomposition"),
                H("The projective classes biject with the cyclic-axis orbits"),
                StatementSource.FromAuthor(AxisDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each quadratic class is in finite bijection with the corresponding A5 "
                        + "axis orbit. The equivalences are noncanonical cardinality matches; "
                        + "no real-geometric or equivariant map is asserted."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("cyclic-axes-degenerate-orders"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/IcosahedralAxisDecomposition."
                        + "cyclic_axes_degenerate_orders"),
                H("The degenerate order parameters are explicit"),
                StatementSource.FromAuthor(DegenerateOrderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At parameter zero all 59 nonidentity elements pass the generator test; "
                        + "at parameter one none do. This records the degenerate inputs."))),
                DescribeRole.Theorem
            ))));

    private static Formula ProjectivePlaneCardinality() => Disp(Seq(
        Card(F.Id("Projectivization")), Sp, Eq, Sp, D(3, 1), Sp, Land, Sp,
        Card(F.Id("FiniteProjectivePlane")), Sp, Eq, Sp, D(3, 1), Dot));

    private static Formula ProjectivePartition() => Disp(Seq(
        UnionOf(UnionOf(ProjectiveClass(D(5)), ProjectiveClass(D(3))),
            ProjectiveClass(D(2))), Sp, Eq, Sp, F.Id("FiniteProjectivePlane"), Sp, Land, Sp,
        F.Id("pairwiseDisjoint"), Open, ProjectiveClass(D(5)), Comma, Sp,
        ProjectiveClass(D(3)), Comma, Sp, ProjectiveClass(D(2)), Close, Dot));

    private static Formula ProjectiveClassCardinalities() => Disp(Seq(
        Card(ProjectiveClass(D(5))), Sp, Eq, Sp, D(6), Sp, Land, Sp,
        Card(ProjectiveClass(D(3))), Sp, Eq, Sp, D(1, 0), Sp, Land, Sp,
        Card(ProjectiveClass(D(2))), Sp, Eq, Sp, D(1, 5), Dot));

    private static Formula AxisOrbitFormula() => Disp(Seq(
        Card(CyclicClass(D(5))), Sp, Eq, Sp, D(6), Sp, Land, Sp,
        Card(CyclicClass(D(3))), Sp, Eq, Sp, D(1, 0), Sp, Land, Sp,
        Card(CyclicClass(D(2))), Sp, Eq, Sp, D(1, 5), Sp, Land, Sp,
        F.Id("eachClassIsOneConjugacyOrbit"), Dot));

    private static Formula AxisStabilizerFormula() => Disp(Seq(
        Card(F.Id("Normalizer5")), Sp, Eq, Sp, D(1, 0), Sp, Land, Sp,
        Card(F.Id("Normalizer3")), Sp, Eq, Sp, D(6), Sp, Land, Sp,
        Card(F.Id("Normalizer2")), Sp, Eq, Sp, D(4), Sp, Land, Sp,
        F.Id("Normalizer2"), Sp, Eq, Sp, F.Id("Centralizer2"), Dot));

    private static Formula AxisDecompositionFormula() => Disp(Seq(
        ProjectiveClass(D(5)), Sp, Sim, Sp, CyclicClass(D(5)), Sp, Land, Sp,
        ProjectiveClass(D(3)), Sp, Sim, Sp, CyclicClass(D(3)), Sp, Land, Sp,
        ProjectiveClass(D(2)), Sp, Sim, Sp, CyclicClass(D(2)), Dot));

    private static Formula DegenerateOrderFormula() => Disp(Seq(
        Card(CyclicClass(D(0))), Sp, Eq, Sp, D(5, 9), Sp, Land, Sp,
        Card(CyclicClass(D(1))), Sp, Eq, Sp, D(0), Dot));

    private static Formula Card(Formula carrier) => Seq(
        Operatorname, Grp(F.Id("card")), Open, carrier, Close);

    private static Formula ProjectiveClass(Formula order) =>
        new Formula.Subscript(F.Id("P"), order);

    private static Formula CyclicClass(Formula order) =>
        new Formula.Subscript(F.Id("A"), order);

    private static Formula UnionOf(Formula left, Formula right) => Seq(
        Operatorname, Grp(F.Id("union")), Open, left, Comma, Sp, right, Close);
}
