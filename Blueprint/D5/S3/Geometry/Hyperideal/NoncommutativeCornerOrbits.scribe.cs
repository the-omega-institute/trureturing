using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class NoncommutativeCornerOrbitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual corner relation of the noncommutative face pairing is the specified subgroup orbit relation.",
        H("Noncommutative actual corner orbits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-act"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.act"),
                H("Right action convention"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G, type Omega and left action of the opposite group on Omega, act(x,g) is op(g) acting on x. Thus it represents the right action of G on Omega."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-act-one"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.act_one"),
                H("Identity acts trivially"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every x in Omega, act(x,1)=x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-act-mul"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.act_mul"),
                H("Composition of right actions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every x in Omega and g,h in G, act(act(x,g),h)=act(x,g*h). The multiplication order is that of a right action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-facepair"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.facePair"),
                H("The actual whole-face pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary u,v in G, the face pairing sends (x,0) to (act(x,u),3), (x,1) to (act(x,v),2), (x,2) to (act(x,v inverse),1), and (x,3) to (act(x,u inverse),0)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-slotmap"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.slotMap"),
                H("The actual corner slot maps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For omitted faces 0,1,2,3, respectively, the permutations of the three increasing corner slots are [0,1,2], [2,0,1], [1,2,0], and [0,1,2]. The displayed nonidentity maps are inverse to one another."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-pairing"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.pairing"),
                H("A whole-face Pairing in the existing interface"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any u,v in G, the whole-face table and slot maps form ActualCornerTransport.Pairing Omega. The face involution is fixed point free because the omitted-face labels change. Its corner-slot maps obey the required inverse compatibility. No freeness, finiteness, transitivity or generation assumption is required."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-normalize"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.normalize"),
                H("The representative sheet of a corner"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For u in G and an actual corner c=(x,j), normalize(u,c)=act(x,u to the natural power j.val). This is a sheet in Omega, not a new definition of the actual corner equivalence relation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-sword"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.sWord"),
                H("The first boundary return word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For u,v in G, sWord(u,v)=(u squared) inverse times v."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-tword"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.tWord"),
                H("The second boundary return word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For u,v in G, tWord(u,v)=(u cubed) inverse times v times u, in this order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-kword"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.kWord"),
                H("The third boundary return word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For u,v in G, kWord(u,v)=v times u cubed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-boundarygroup"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.boundaryGroup"),
                H("The subgroup generated by the three return words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For u,v in G, boundaryGroup(u,v) is Subgroup.closure of the set containing sWord(u,v), tWord(u,v) and kWord(u,v). It is the subgroup generated by these words, with no normal-closure operation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-actual-step"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.actual_step"),
                H("The original face-slot corner step"),
                StatementSource.FromAuthor(F.Disp(ActualStepFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here G ranges over all groups and Omega over all types equipped with a left action of the opposite group, written as a right action of G. For every u,v in G, x in Omega, f in Fin(4) and r in Fin(3), the displayed corners are related in the equivalence closure of the original cornerRel for pairing(u,v). Fin(n) means the integers from zero through n-1, and first and second denote pair projections. No finiteness, faithfulness or freeness assumption is imposed. This existing helper is now public for direct reuse by ActualLinkCornerChains.move_carrier. Its statement and proof are unchanged: each actual face slot supplies a generator of the original corner EqvGen. The affine link construction uses this exact step to preserve the same corner-class tag; no copied private proof or alternative orbit relation is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noncommutative-corner-actual-corner-orbit-iff"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.actual_corner_orbit_iff"),
                H("Actual corner equivalence is exactly the subgroup orbit relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every group G, arbitrary type Omega with an action of the opposite group, u,v in G and actual corners c,d in Omega times Fin(4), the equivalence closure of ActualCornerTransport.cornerRel for pairing(u,v) relates c and d if and only if there exists g in boundaryGroup(u,v) with act(normalize(u,c),g)=normalize(u,d). The proof constructs actual face-slot paths from each corner to its normalized corner at vertex zero, constructs actual paths for the three subgroup generators, extends those paths over subgroup products and inverses, and proves that every original face-slot generator preserves the specified orbit relation. Empty Omega, infinite groups, nonfaithful actions and stabilizers are included. This statement supplies the corner-relation characterization only; it does not assert edge periods, Euler characteristic, surface links, manifold charts or a geometric metric."))),
                DescribeRole.Theorem),
            Paragraph(Text("The regular SL(2,F_5) application takes u=[[0,1],[4,1]] and v=[[1,1],[0,1]]. The low return v inverse times u squared is [[0,1],[4,0]], and the high return v squared times u is [[3,3],[4,1]]. Their squares and cubes, respectively, are minus the identity and the identity. The high return is nonidentity, so the return orders are four and three. Also u cubed is minus the identity, v to the fifth power is the identity and v is nonidentity, and u*v is the low return.")),
            Paragraph(Text("The powers of v give every upper transvection over F_5. Conjugating the upper transvection with parameter minus c by the low return gives the lower transvection with parameter c. Matrix.SL2.transvection_induction therefore puts every determinant-one matrix in the subgroup generated by u and v. This group has 120 elements: its first column has 24 nonzero choices, and each first column admits five second columns with determinant one.")),
            Paragraph(Text("For these same matrices, write s=(u squared) inverse times v and k=v times u cubed, using the actual sWord and kWord. The identities s squared times k=v and s inverse times v inverse=u show that boundaryGroup contains both original generators. Since boundaryGroup is the subgroup generated by sWord, tWord and kWord, it equals the entire SL(2,F_5).")),
            Paragraph(Text("In a field of characteristic different from two, a determinant-one two-by-two matrix A with A squared equal to the identity is either the identity or minus the identity. Indeed A inverse=A, while the explicit inverse interchanges the diagonal entries and negates the off-diagonal entries. Thus the diagonal entries agree, the off-diagonal entries vanish, and the determinant forces the diagonal scalar to have square one. In SL(2,F_5), minus the identity is nonidentity and has order two.")),
            Paragraph(Text("Matrix.SpecialLinearGroup.mem_center_iff identifies the center of SL(2,F_5) with the identity and minus the identity. If the image of an arbitrary A in the native quotient PSL(2,F_5) is nonidentity with square one, then A squared lies in this center. A squared cannot be the identity, since the preceding classification would make A itself central. Hence A squared is minus the identity and A has order four. This conclusion applies to every lift of the given projective element.")),
            Paragraph(Text("These algebraic relations supply the marked matrices, generation, central-lift orders and the actual corner return subgroup. Geometric realization, actual edge-cycle degrees, link-surface counts and genus require their corresponding face-pairing and topology arguments.")))));

    private static Formula ActualStepFormula()
    {
        var group = F.Id("G"); var omega = F.Id("Omega");
        var u = F.Id("u"); var v = F.Id("v"); var x = F.Id("x");
        var f = F.Id("f"); var r = F.Id("r");
        var image = Call("facePair", u, v, Pair(x, f));
        var conclusion = Call("EqvGen", Call("cornerRel", Call("pairing", u, v)),
            Pair(x, Call("faceVertex", f, r)),
            Pair(Call("first", image),
                Call("faceVertex", Call("second", image), Call("slotMap", f, r))));
        return All("G", F.Id("Group"),
            All("Omega", Call("RightAction", group),
                All("u", group, All("v", group, All("x", omega,
                    All("f", Call("Fin", F.D(4)),
                        All("r", Call("Fin", F.D(3)), conclusion)))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Pair(Formula left, Formula right) =>
        F.Seq(F.Open, left, F.Comma, F.Sp, right, F.Close);
}
