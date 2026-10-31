using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/PolygonEarSlide.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual polygon condition preserving ear slide",
        H("Actual polygon carrier and cyclic order"),
        Blocks(
            Describe.Lean(DescribeId.Create("polygon-ear-slide-carrier"),
                DeclarationHandle.Create(Prefix + "IsTriangulation"), H("Actual maximal diagonal carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Vertices are ZMod n and chords are unordered pairs. Internal diagonals are segments that are not boundary sides. Cross records the two cyclic betweenness witnesses, and an actual triangulation is a maximal noncrossing finite set of internal diagonals."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-rotation"),
                DeclarationHandle.Create(Prefix + "isTriangulation_map_add"), H("Cyclic translation of triangulations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Adding a fixed vertex offset to every chord preserves internal diagonals, crossing, noncrossing, and maximality. The proof pulls every candidate diagonal back by the inverse offset."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-swap-transport"),
                DeclarationHandle.Create(Prefix + "cross_chordSwap_of_avoidTwo"), H("Crossing transport away from the deleted centre"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vertex permutation exchanges 1 and 2. A chord whose endpoints avoid 2 remains in the cyclic coordinate order after this exchange, including the cyclic seam, so crossing is preserved in both directions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-exclusion"),
                DeclarationHandle.Create(Prefix + "avoidTwo_of_mem_triangulation"), H("Ear-centre exclusion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If t={1,3} belongs to an actual triangulation, every internal diagonal incident with 2 crosses t and is absent. The analogous statement for s={0,2} excludes the exchanged centre."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-map"),
                DeclarationHandle.Create(Prefix + "phi"), H("Concrete erase, swap, and insert map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map phi erases t, applies the vertex exchange to every retained chord, and inserts s. The inverse psi erases s, applies the same exchange, and inserts t. The inserted chord is treated separately in the maximality proofs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-triangulation"),
                DeclarationHandle.Create(Prefix + "phi_isTriangulation"), H("Actual triangulation preservation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every source triangulation containing t, phi is an actual triangulation. Diagonal and noncrossing preservation use the exclusion of centre 2; maximality pulls a target candidate back through the exchange and handles the fresh chord s separately. The corresponding statement holds for psi."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-inverse"),
                DeclarationHandle.Create(Prefix + "psi_phi"), H("Inverse laws on complete chord sets"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the actual diagonal membership and ear containment conditions, psi(phi T)=T and phi(psi U)=U. These are equalities of complete finite chord sets, so no selected completion or witness is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-trace"),
                DeclarationHandle.Create(Prefix + "trace_phi"), H("Exact observed-ear trace transport"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every ear centre outside 0,1,2,3 is fixed by the vertex exchange. The source trace containing centre 2 therefore becomes the target trace containing centre 1 after erasing centres 2 and 3 from the observed set; centre 3 is free on the target side. The inverse trace statement is proved independently."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-fixed-fibre"),
                DeclarationHandle.Create(Prefix + "condition_fibre_equiv"), H("Normalized condition fibre equivalence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least 14, disjoint compatible forced and forbidden ear sets P and Q of cardinalities (2,2), (3,3), (2,4), or (4,2), and an observed set J inside the compatible carrier E_K, the subtype of all actual triangulations with trace insert 2 R is equivalent to the subtype with trace insert 1 R on J.erase 2.erase 3. Empty subtypes are included. The P, Q, and R coordinates are discharged from the carrier hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-arbitrary-placement"),
                DeclarationHandle.Create(Prefix + "condition_fibre_equiv_at"), H("Arbitrary cyclic block placement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any cyclic start a, conjugating the normalized equivalence by verified translation gives the full fibre equivalence with source trace insert (a+2) R and target trace insert (a+1) R on J.erase (a+2).erase (a+3). All actual triangulation completions and infeasible fibres remain in the two subtype fibres."))),
                DescribeRole.Theorem)), []));
}
