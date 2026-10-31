using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.TauCeti.Algebra.Homology;

internal sealed class TotalComplexDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);
    private static Formula Down => Call("down", V("Nat"));
    private static Formula RowMap => Call("map", Call("mapHomologicalComplex",
        Call("eval", V("C"), Down, V("q")), Down), V("phi"));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(All("C", Call("Type", V("u"))), Inst("Category", V("v"), V("C")),
            Inst("Abelian", V("C"))),
        Seq(All("K", Call("HomologicalComplex2", V("C"), Down, Down)),
            All("L", Call("HomologicalComplex2", V("C"), Down, Down)),
            All("phi", Call("Hom", V("K"), V("L")))),
        Seq(Open, All("q", V("Nat")), Call("QuasiIso", RowMap), Close,
            Sp, Rightarrow, Sp,
            Call("QuasiIso", Call("totalMap", V("phi"), Down)))
    ]));
    private static AssessedProvenance Source => AssessedProvenance.FromLiterature(
        LibraryNoteRef.Create("D5/L/Topology/tauceti2026totalcomparison"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rowwise quasi-isomorphisms give quasi-isomorphisms of first-quadrant total complexes.",
        H("First-quadrant row-to-total comparison"), Blocks(
            Paragraph(Text("The object universe u and morphism universe v are independent. "
                + "The coefficient category C is any abelian category. A bicomplex K has objects K(p,q) "
                + "for natural p and q, with commuting horizontal and vertical differentials lowering "
                + "their respective indices. Its row q is the horizontal chain complex obtained by "
                + "evaluating each column at q. A bicomplex morphism phi supplies actual maps of these rows.")),
            Describe.Lean(DescribeId.Create("row-to-total-quasi-isomorphism"),
                DeclarationHandle.Create("D5/S3/Topology/TauCeti/Algebra/Homology/TotalComplex.quasiIso_total_map_of_rows"),
                H("Comparison of the actual total maps"), StatementSource.FromAuthor(Statement), Source,
                Blocks(
                    Paragraph(Text("In degree n, the native total complex is the coproduct of K(p,q) over "
                        + "p+q=n. This antidiagonal is finite, so the finite coproducts already available in an "
                        + "abelian category suffice. On its (p,q) summand the differential is d1 plus "
                        + "(-1)^p times d2. totalMap is the map induced on these same coproducts by phi; "
                        + "it is the native HomologicalComplex2.total.map, with no alternative totalization.")),
                    Paragraph(Text("Assume every horizontal row map is a quasi-isomorphism. Then totalMap "
                        + "induces an isomorphism on homology in every natural degree, including zero. "
                        + "There is no bounded-support, bounded-length, exact-infinite-coproduct, AB4, "
                        + "field or module hypothesis. Zero objects and empty antidiagonal summands are included.")),
                    Paragraph(Text("Row zero includes as a subcomplex of Tot(K). Delete it and reindex row q+1 "
                        + "as row q to obtain rowsSucc(K). The quotient is the native extension by zero of "
                        + "Tot(rowsSucc(K)) along n mapped to n+1; its object in degree zero is zero. "
                        + "Deleting a row preserves p and therefore preserves the vertical sign (-1)^p. "
                        + "This extension uses the original differential and is not a signed suspension.")),
                    Paragraph(Text("Splitting each antidiagonal into its row-zero summand and its positive-row "
                        + "summands gives a degreewise split short exact sequence. These sequences commute with "
                        + "the actual maps induced by phi. Their homology sequences give a simultaneous induction: "
                        + "Tot(phi) induces isomorphisms below Q and an epimorphism in degree Q. At Q=0 the "
                        + "quotient has zero homology in degree zero. For the successor step, apply the preceding "
                        + "bound to the remaining rows and transport homology along extension by zero. The "
                        + "middle-map diagram lemmas then supply both assertions. For any requested degree m, "
                        + "choose Q=m+1 to obtain its homology isomorphism.")),
                    Paragraph(Text("This is the relative acyclic assembly statement cited by the Tau Ceti "
                        + "source with a pointer to Weibel, Section 2.7. It supplies the general comparison "
                        + "step for later augmented-row and Cech constructions. It asserts no singular-chain "
                        + "augmentation or descent theorem by itself."))), DescribeRole.Theorem))));
}
