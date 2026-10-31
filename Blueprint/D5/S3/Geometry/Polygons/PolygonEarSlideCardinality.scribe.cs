using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact complete-fibre local polygon ear-slide counts",
        H("Complete conditioned fibres at every cyclic block origin"),
        Blocks(Describe.Lean(DescribeId.Create("polygon-ear-slide-cardinality-at"),
            DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonEarSlideCardinality.condition_fibre_card_at"),
            H("Exact local law with the optional third-ear fibre"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("For n at least 14, P and Q are arbitrary forced and forbidden ear-centre sets. J is a subset of E_K(P union Q), a is absent from J, and a+1,a+2 belong to J. R is supported on J with a+1,a+2,a+3 erased. Nat.card counts the complete ConditionFiber subtype of actual maximal noncrossing finite diagonal sets. Thus infeasible and empty fibres are included.")),
                Paragraph(Text("Write s=a+1, t=a+2, u=a+3. The complete fibre with trace R+t is equivalent, by condition_fibre_equiv_at, to the fibre with trace R+s on J with t,u erased. Every member of that reduced fibre contains s and therefore excludes t, since those actual ears cross. Restoring the observations in J leaves only the choice whether u occurs. When u belongs to J, the two disjoint branches are exactly the original full fibres with traces R+s and R+s+u. Otherwise there is just the R+s fibre. Both branch maps preserve the entire original chord set, P, and Q.")),
                Paragraph(Text("This is the local complete-count law (37.8) of the pinned theory AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY, B-37.2, at source revision 7a72936968c08198f04951d1326bfd4dd891e804. The four source cases (|P|,|Q|)=(2,2),(3,3),(2,4),(4,2), with disjoint compatible P,Q, are special cases; these extra restrictions are unnecessary for the local law. Exchanging P and Q gives a separate instance using E_K(Q union P)=E_K(P union Q). No equality between the two sides' weights is asserted or used.")),
                Paragraph(Text("The result supplies neither global conditional-count positivity, normalized strict inequality or its equality case, nor terminal independent nonempty support. It does not formalize the remainder of B-37.2. Existing-theory atom decomposition and deposit or coverage are separate pending operations. ite(c,x,y) in the formula means x if c holds and y otherwise; SymTwo and EK in the companion document denote Sym2 and E_K."))), DescribeRole.Theorem)), []));

    private static Formula Count(Formula trace) => C("Natcard", Fibre(X("J"), trace));
    private static Formula Statement() => Scope(All("a", Vertex, SetsAll(
        Imp(Lower(14), Imp(SubF(X("J"), C("EK", Union(X("P"), X("Q")))), LocalHyp(true,
            EqF(Count(Insert(Pos(true, 2), X("R"))),
                Add(Count(Insert(Pos(true, 1), X("R"))),
                    C("ite", InF(Pos(true, 3), X("J")),
                        Count(Insert(Pos(true, 3), Insert(Pos(true, 1), X("R")))), N(0))))))),
        "P", "Q", "J", "R")));
}
