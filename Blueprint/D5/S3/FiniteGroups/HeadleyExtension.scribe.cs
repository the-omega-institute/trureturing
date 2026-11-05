using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyExtensionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/HeadleyExtension.";

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula CycleType(bool star)
    {
        var g = F.Id("G");
        var signature = Seq(Call(star ? "RStar" : "RCycle", g), Colon, F.Id("Type"));
        return All("G", F.Id("Type"), Seq(Instance("AddCommGroup", g),
            star ? Seq(Instance("Finite", g), signature) : signature));
    }
    private static Formula ExtensionClaim()
    {
        var e = F.Id("E"); var n = F.Id("N");
        return All("E", F.Id("Type"), Seq(Instance("AddCommGroup", e), Instance("Fintype", e),
            All("N", Call("AddSubgroup", e), new Formula.TypeArrow(Call("RCycle", n),
                new Formula.TypeArrow(Call("RStar", Seq(e, Slash, n)),
                    Call("Nonempty", Call("RCycle", e)))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An R-cycle on a kernel and an even R-star quotient construct a cyclic ordering with every nonzero directed difference in an arbitrary finite abelian extension.",
        H("Headley nonsplit extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("headley-extension-r-cycle"),
                DeclarationHandle.Create(Owner + "RCycle"),
                H("A complete cyclic vertex and directed-difference inventory"),
                StatementSource.FromAuthor(Disp(CycleType(false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RCycle(G) is the type of records consisting of permutations S and Delta of G, the equality S(0)=0, the assertion that S is one cycle on all nonzero elements, and the equation Delta(x)=S(x)-x for every x in G. Thus Delta fixes zero and restricts to a bijection of the nonzero elements. Every edge is recorded, including the closing edge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-extension-r-star"),
                DeclarationHandle.Create(Owner + "RStar"),
                H("A quotient cycle with the additive triple used by the splice"),
                StatementSource.FromAuthor(Disp(CycleType(true))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RStar(G) extends RCycle(G) with even cardinality and three pairwise distinct nonzero vertices a,b,c. Its successor satisfies S(a)=b and S(b)=c, and a+c=b. Evenness is included in this interface; no additional condition is imposed on the kernel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-nonsplit-extension-r-cycle"),
                DeclarationHandle.Create(Owner + "nonsplit_extension_r_cycle"),
                H("The kernel cycle is inserted by a two-row splice"),
                StatementSource.FromAuthor(Disp(ExtensionClaim())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be any finite additive abelian group and N a subgroup. An R-cycle on N and an R-star cycle on the even quotient E/N imply an R-cycle on E. Representatives A,C of a,c are arbitrary, B=A+C, and the other representatives are arbitrary. The representative map has no additivity requirement, so nonsplit extensions are included. A trivial kernel is handled by the additive quotient equivalence.")),
                    Paragraph(Text(
                        "Extend the kernel successor D by D(0)=0 and put F(h)=h-D(h), J=F inverse. Both F and J are orthomorphisms. The a-to-b and b-to-c lifts use F,J. The next edge uses D and the remaining edges use consecutive F,J pairs. Even quotient order makes their number even, so the unmodified return is D.")),
                    Paragraph(Text(
                        "Choose v nonzero in N. Replace row zero by A,D(v),D squared(v),...,v,C+v. Replace row v by A+v,B+F(v),B,C. These are the same successor changes as two transpositions at the vertices A, v, and B+F(v). They join the zero row, the nonzero kernel cycle, and the remaining nonzero rows into one cycle. The proof identifies the actual first positive return to the A-column and excludes an intervening visit to that column. Its return permutation is D composed with the transposition of zero and v, whose cyclic traversal is zero,D(v),D squared(v),...,v.")),
                    Paragraph(Text(
                        "For every ordinary edge the quotient difference identifies its coset, and the orthomorphism difference bijects that coset. The splice permutes three old labels: the label C, the cut kernel label D(v)-v, and the label -A+D(v). The fourth cross-column label C-D(v) is unchanged. The inverse three-cycle on source indices therefore gives a full ambient directed-difference bijection, rather than only a quotient inventory.")),
                    Paragraph(Text(
                        "This construction belongs to the R-sequenceability program of P. Headley, R-sequenceability and R-star-sequenceability of abelian 2-groups, Discrete Mathematics 131, 345-350, DOI 10.1016/0012-365X(94)90396-4. The explicit splice is a reconstruction; no originality claim is made. The theorem supplies the extension step only. Elementary and order-eight bases, induction through abelian 2-groups, and the R-star quotient construction with arbitrary odd factors are additional obligations for the full Headley supplier. The arbitrary-subset sequencing problem is outside this theorem."))),
                DescribeRole.Theorem))));
}
