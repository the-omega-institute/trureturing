using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalLatticeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal middle letters define an index-c congruence lattice. A shortest vector extends by Bezout to an oriented basis; centering the second vector gives bounded integer coordinates for every point in the original endpoint box. Dyadic scales supply the J1,J2 assumptions and the actual endpoint coefficient and pencil-height bounds. This is the long-chart lattice bridge, not the original six-tuple count.",
        H("Original prime-cube lattice"),
        Blocks(
            Paragraph(Text("For unit w modulo c, the physical endpoint lattice consists of (u,z) with w z - t u divisible by c. The anchor (-w,-t) belongs to this lattice and to the same literal box as the endpoints. The chosen metric has squared norm (Y/X)u^2+(X/Y)z^2 and determinant one; no fixed input unit is absorbed into an interval.")),
            Paragraph(Text("The proof takes a minimum in the finite weighted ball containing (c,0). The shortest vector is primitive in the explicit congruence basis, so Bezout completes it to an oriented determinant-c basis. An integer shift centers the second vector. The determinant identity gives 3 Q(R)^2 <= 4 c^2 and Q(R)Q(V) <= 2 c^2. Determinant bounds then place every literal endpoint and the anchor within the stated CoordinateBound rectangle.")),
            Paragraph(Text("For a long chart, a dyadic s0 satisfies s0^2 <= Q(R) < 4 s0^2. With H^2=XY, J1=8H/s0 and J2=4Hs0/c satisfy J2<=J1, J2>2, J1 J2=32XY/c and J1<16XY/c. These scales realize the original endpoint coefficient constant 3 and pencil height 18. The theorem does not infer that the shortest vector has unit coordinates; that is a separate chart condition required by later residue formulas.")),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-middle-lattice"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.middleLattice"),
                H("Physical congruence lattice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Literal integer pairs satisfying w z - t u = 0 modulo c."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-middle-basis"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.MiddleBasis"),
                H("Oriented integer basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("An oriented determinant-c basis with integer decomposition of every physical lattice point."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-unit-basis"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.middleBasis_of_unit"),
                H("Explicit unit-slope basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("A unit w modulo c supplies the kernel basis (1,k),(0,c), where k=t/w modulo c."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-weighted-identity"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.weighted_det_identity"),
                H("Weighted determinant identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The area-preserving anisotropic metric satisfies Q(z)Q(z')-dot(z,z')^2=det(z,z')^2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-shortest"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_shortest_middle_vector"),
                H("Shortest physical vector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("A finite weighted ball gives a shortest nonzero vector in the actual congruence lattice."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-reduced-basis"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_reduced_middle_basis"),
                H("Reduced oriented basis exists"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The shortest vector is primitive in the kernel basis; Bezout completion and an integer centering shift give a reduced oriented basis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-reduction-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.ReducedMiddleBasis.reduction_bounds"),
                H("Reduced basis constants"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Shortestness and centering imply 3 Q(R)^2 <= 4 c^2, Q(R)<2c and Q(V)Q(R)<=2c^2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-coordinate-bound"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.ReducedMiddleBasis.coordinate_bound"),
                H("Literal endpoint coordinate bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Each point in the original X by Y box has integral reduced coordinates bounded by J1 and J2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-long-scales"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.ReducedMiddleBasis.long_scale_bounds"),
                H("Long-chart scale relations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The long condition and dyadic reduced length imply J2<=J1, J2>2, J1 J2=32XY/c and J1<16XY/c."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-dyadic"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.exists_dyadic_middle_scale"),
                H("Dyadic reduced-length scale"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("A positive squared length has a power-of-two scale s0 with s0^2<=A<4s0^2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-original-lattice-endpoint-inputs"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLattice.ReducedMiddleBasis.actual_endpoint_inputs"),
                H("Actual coefficient and height inputs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Literal box membership for the anchor, baseline and endpoint supplies factor-cover scale order, endpoint coefficients with C=3, and actual pencil height H=18."))), DescribeRole.Theorem)),
        edges: []));
}
