using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.TauCeti.Algebra.Homology;

internal sealed class FiniteDegreeComparisonDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);
    private static Formula Down => Call("down", V("Nat"));
    private static Formula ColHom => Call("homologyMap", Call("columnMap", V("phi"), V("p")), V("q"));
    private static Formula TotalHom(Formula n) =>
        Call("homologyMap", Call("totalMap", V("phi"), Down), n);
    private static Formula Sum => Seq(V("p"), Sp, Plus, Sp, V("q"));
    private static Formula Next => Seq(V("k"), Sp, Plus, Sp, Num(1));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(All("C", Call("Type", V("u"))), Inst("Category", V("v"), V("C")),
            Inst("Abelian", V("C"))),
        Seq(All("k", V("Nat")),
            All("K", Call("HomologicalComplex2", V("C"), Down, Down)),
            All("L", Call("HomologicalComplex2", V("C"), Down, Down)),
            All("phi", Call("Hom", V("K"), V("L")))),
        Seq(Open, All("p", V("Nat")), All("q", V("Nat")), Sum, Sp, Le, Sp, V("k"),
            Sp, Rightarrow, Sp, Call("IsIso", ColHom), Close, Sp, Rightarrow),
        Seq(Open, All("p", V("Nat")), All("q", V("Nat")), Sum, Sp, Eq, Sp, Next,
            Sp, Rightarrow, Sp, Call("Epi", ColHom), Close, Sp, Rightarrow),
        Seq(Open, All("n", V("Nat")), V("n"), Sp, Le, Sp, V("k"), Sp, Rightarrow, Sp,
            Call("IsIso", TotalHom(V("n"))), Close, Sp, Land, Sp, Call("Epi", TotalHom(Next)))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangular column homology comparison controls native total homology through a finite degree.",
        H("Finite-degree bicomplex comparison"), Blocks(
            Paragraph(Text("Let C be any abelian category with independent object universe u and morphism "
                + "universe v. Let K and L be bicomplexes indexed by two natural numbers, with both "
                + "differentials lowering their respective index. The column p is the actual complex K.X p, "
                + "and columnMap(phi,p) is phi.f p. Its degree-q homology map is the native homologyMap.")),
            Describe.Lean(DescribeId.Create("finite-degree-column-total-comparison"),
                DeclarationHandle.Create("D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison.finite_degree_comparison_total_map"),
                H("Isomorphisms below the boundary and epimorphism on it"),
                StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Topology/tauceti2026totalcomparison")),
                Blocks(
                    Paragraph(Text("Assume the actual column homology map is an isomorphism when p+q is at "
                        + "most k and an epimorphism when p+q=k+1. Then the actual total map is an isomorphism "
                        + "on homology in every degree n at most k and an epimorphism in degree k+1. "
                        + "The boundary epimorphisms are part of the hypotheses and the conclusion. "
                        + "No condition is imposed above that boundary, and no entire row or column is "
                        + "required to be a quasi-isomorphism.")),
                    Paragraph(Text("The total object in degree n is the native finite coproduct over p+q=n, "
                        + "and totalMap(phi,down(Nat)) is HomologicalComplex2.total.map on these same "
                        + "coproducts. The differential on the (p,q) summand is d1+(-1)^p d2. "
                        + "Finite antidiagonals supply the needed coproducts in every abelian category. "
                        + "There is no bound on the set of columns or on the support, and no supplied "
                        + "convergence theorem, comparison hypothesis, field or module restriction.")),
                    Paragraph(Text("First prove a row version by simultaneous induction on Q: row-homology "
                        + "isomorphisms at p+q<Q and epimorphisms at p+q=Q imply total-homology "
                        + "isomorphisms below Q and an epimorphism at Q. Row zero includes into the total. "
                        + "The quotient is the extension by zero of Tot(rowsSucc(K)) along n mapped to n+1. "
                        + "The short exact sequence splits in each degree, naturally in the bicomplex map. "
                        + "At Q=0 its quotient has zero homology in degree zero, so row-zero surjectivity "
                        + "gives the required epimorphism.")),
                    Paragraph(Text("For Q+1, apply the induction hypothesis to rowsSucc, whose row q is the "
                        + "original row q+1. Its triangular bounds are exactly those for Q after reindexing. "
                        + "Extension by zero gives the quotient isomorphisms in degrees below Q+1 and "
                        + "epimorphisms through Q+1, including the preceding degree needed by the middle-map "
                        + "isomorphism lemma. On row zero, the bounded hypotheses supply the isomorphism "
                        + "at the requested degree, the monomorphism in the following degree, and the "
                        + "boundary epimorphism. The local homology-sequence diagram lemmas then give both "
                        + "total assertions. Deleting a row preserves p, so the quotient keeps the sign "
                        + "(-1)^p; this extension is not a signed suspension.")),
                    Paragraph(Text("Flip the bicomplex so that its rows are the original columns, with their "
                        + "actual maps phi.f p. The native totalFlipIso identifies the flipped total with "
                        + "the original total by multiplication by (-1)^(p*q) on each summand. Its naturality "
                        + "identifies the total of the flipped morphism with the actual total morphism. "
                        + "Apply the row induction at Q=k+1 and transport homology across this signed "
                        + "isomorphism to obtain precisely the stated column result.")),
                    Paragraph(Text("This is a standard general finite-degree comparison theorem. The row-zero "
                        + "decomposition and local transfer statements come from the cited Tau Ceti sources; "
                        + "the bounded induction composes them here. This theorem alone makes no claim about "
                        + "an augmentation, a nerve, an open cover, or a singular-chain construction."))),
                DescribeRole.Theorem))));
}
