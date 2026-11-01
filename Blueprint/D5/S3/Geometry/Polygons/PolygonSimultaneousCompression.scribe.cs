using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideCardinalityFormula;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonCompressionFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonSimultaneousCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common-support terminal compression of original polygon triangulation families",
        H("Common-support terminal compression of original polygon triangulation families"),
        Blocks(
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-deletionsystem"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.deletionSystem"),
                H("deletionSystem"), StatementSource.FromAuthor(Disp(Sc(SetsAll(Imps(C("DeletionSystem",C("EK",Union(X("P"),X("Q")))) ,Lower(14),Nonempty(Union(X("P"),X("Q")))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For n at least 14 and nonempty P union Q, this constructs the actual DeletionSystem on J=E_K(P union Q). At every H subset J its feasible universe is all independent subsets, its terminal predicate is Independent H, and its left/right weights are respectively weight P Q H and weight Q P H. Nonnegativity is cardinal nonnegativity. feasible_projection and marginal_weight realize all deletion fields. Properness and block_start choose a with a absent and a+1,a+2 present. The coordinates s=a+1,t=a+2,u=a+3 are distinct as required; local_excludes and shift_mem_feasible supply geometry. local_weight_law supplies the left law and, using union_comm on E_K, a separate right law. No weight equality is assumed. The displayed formula gives the constructor type; these field assignments specify its value."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-wholefiber"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.WholeFiber"),
                H("WholeFiber"), StatementSource.FromAuthor(Disp(Sc(SetsAll(EqF(Whole(X("P"),X("Q")),C("ConditionFiber",X("P"),X("Q"),C("empty"),C("empty"))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("WholeFiber P Q is the subtype of all actual triangulations forcing P and forbidding Q, with the vacuous exact trace on the empty observation support. Families are arbitrary finite subsets of this subtype."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-familytraces"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces"),
                H("familyTraces"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("A",C("Finset",Whole(X("P"),X("Q"))),All("X",Sets,IffF(InF(X("X"),Traces(X("H"),X("A"))),ExistsF("T",Whole(X("P"),X("Q")),Cj(InF(X("T"),X("A")),EqF(X("X"),Inter(Ears(C("val",X("T"))),X("H")))))))),"P","Q","H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The image contains precisely the observed ear traces of selected original members. It does not replace a partial fibre by a full fibre at the level of the original family."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-familytraces-feasible"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces_feasible"),
                H("familyTraces feasible"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("A",C("Finset",Whole(X("P"),X("Q"))),Imp(Lower(6),SubF(Traces(X("H"),X("A")),Omega(X("H"))))),"P","Q","H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every image trace is feasible because each original member is an actual triangulation. Feasible traces without completions remain in the universe."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-original-card-le-trace-mass"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.original_card_le_trace_mass"),
                H("original card le trace mass"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("A",C("Finset",Whole(X("P"),X("Q"))),Le(Cast(C("card",X("A"))),Mass(X("P"),X("Q"),X("H"),Traces(X("H"),X("A"))))),"P","Q","H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Finset.card_eq_sum_card_image counts original members fibre by fibre. Each selected fibre injects, by retaining its original triangulation, into the complete ConditionFiber P Q H X. Summing the cardinal bounds gives an inequality. No saturation equality is asserted, and no global positivity or explicit conditional-count formula is needed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-shared-ear-mem-ek"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.shared_ear_mem_EK"),
                H("shared ear mem EK"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("T",Whole(X("P"),X("Q")),All("U",Whole(X("Q"),X("P")),All("i",Vertex,Imps(InF(X("i"),C("EK",Union(X("P"),X("Q")))),InF(X("i"),Ears(C("val",X("T")))),InF(X("i"),Ears(C("val",X("U")))))))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A common ear cannot lie in P or Q, since the opposite member forbids that side. For every k in P use noncrossing in the first triangulation, and for k in Q use the second. Thus the common ear avoids all K ears and belongs to the full allowed E_K K."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-common-ears-eq-trace-inter"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.common_ears_eq_trace_inter"),
                H("common ears eq trace inter"), StatementSource.FromAuthor(Disp(Sc(SetsAll(All("T",Whole(X("P"),X("Q")),All("U",Whole(X("Q"),X("P")),EqF(Inter(Ears(C("val",X("T"))),Ears(C("val",X("U")))),Inter(Inter(Ears(C("val",X("T"))),C("EK",Union(X("P"),X("Q")))),Inter(Ears(C("val",X("U"))),C("EK",Union(X("P"),X("Q"))))))))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This is the full-ear to trace-intersection bridge (source 37.5). It uses the complete E_K(P union Q), rather than a protected subcarrier chosen in advance."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-familytraces-cross"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces_cross"),
                H("familyTraces cross"), StatementSource.FromAuthor(Disp(Sc(SetsAll(FamilyAll(Imp(OriginalCross,C("CrossIntersecting",Traces(C("EK",Union(X("P"),X("Q"))),X("A")),Traces(C("EK",Union(X("P"),X("Q"))),X("B"))))),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Full-ear cross-intersection of opposite original members descends to cross-intersection of their allowed traces, by the exact intersection bridge."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("polygonsimultaneouscompression-exists-original-terminal-compression"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.exists_original_terminal_compression"),
                H("exists original terminal compression"), StatementSource.FromAuthor(Disp(Sc(SetsAll(FamilyAll(Imps(ExistsF("H",Sets,ExistsF("C",Family,ExistsF("D",Family,Cj(
                SubF(X("H"),C("EK",Union(X("P"),X("Q")))),Ind(X("H")),Geometric(X("H")),
                SubF(X("C"),Powers(X("H"))),SubF(X("D"),Powers(X("H"))),C("CrossIntersecting",X("C"),X("D")),
                C("RelativelyUpper",Powers(X("H")),X("C")),C("RelativelyUpper",Powers(X("H")),X("D")),
                Le(Cast(C("card",X("A"))),Mass(X("P"),X("Q"),X("H"),X("C"))),
                Le(Cast(C("card",X("B"))),Mass(X("Q"),X("P"),X("H"),X("D"))),
                Imp(Nonempty(X("A")),Nonempty(X("C"))),Imp(Nonempty(X("B")),Nonempty(X("D"))),
                Imps(Nonempty(X("H")),Nonempty(X("A")),Nonempty(X("B"))))))),Lower(14),Nonempty(Union(X("P"),X("Q"))),OriginalCross)),"P","Q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For n at least 14, arbitrary P,Q with nonempty union, and finite original families A subset WholeFiber P Q and B subset WholeFiber Q P whose opposite members share an ear, there are one common H subset E_K(P union Q) and families C,D on H. H consists of pairwise noncrossing actual ear chords. C,D are cross-intersecting and closed under every superset inside H.powerset. Their separate complete-fibre P|Q and Q|P masses dominate the respective original cardinalities. Each nonempty side stays nonempty; if both inputs are nonempty, a common output ear proves H nonempty. The empty initial E_K case is included: the same implication excludes two nonempty inputs. Apply the existing exists_terminal_compression to deletionSystem; terminal independence identifies feasible H with the entire powerset. This realizes exactly the compression prefix of B-37.2 residual child 82a336ea36dcb1fdf33de82be432b2ef57a5cccb4770e8737a97a557029cda16, bytes [0,1646), parent bb66dfd880da1b1f58a57a9d778dd6406ce5738d2f047f6862da8c62cf8288f6 bytes [4005,5651). The source cases with cardinalities 2,3,4 and disjoint compatible P,Q are included; those extra assumptions are unnecessary here. Rank/count/Catalan bounds, strictness, total-count positivity, inclusion-exclusion Npq and the normalized bound remain outside this theorem. The construction makes no assertion that every independent trace has a triangulation completion, and no identification of the two weights."))), DescribeRole.Theorem)), []));
}
