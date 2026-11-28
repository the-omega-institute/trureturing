using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class OlairezWrapHullDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/olairez2026dihedralpermutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed wrap hull is a linear image of the cross-polytope.",
        H("The signed wrap hull and constant translates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("olairez-wrap-absolute-sum"),
                DeclarationHandle.Create(Module + ".absoluteSum"),
                H("Absolute sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a real vector z with coordinates indexed modulo a positive n, its absolute sum is the sum of the absolute values of its entries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("olairez-wrap-hull-feasibility"),
                DeclarationHandle.Create(Module + ".scaled_wrap_hull_iff"),
                H("Membership in the scaled wrap hull"),
                StatementSource.FromAuthor(MembershipFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("This criterion supports the lattice-point count in Question 6.1 of Colin Olairez, arXiv:2610.28672v2, §6, printed p. 21. Source locator https://arxiv.org/html/2610.28672v2#S6.Thmquestion1 . For a positive natural n, Hₙ is the real sum-zero subspace. Cₙ is the convex hull in Hₙ of the signed wrap vectors ±(1 − neᵢ). The linear map u ↦ (∑ᵢ uᵢ)1 − nu sends the signed coordinate basis to these vectors.")),
                    Paragraph(Text("The absolute-sum unit ball is the convex hull of the signed basis. One convex combination represents each point of the ball using its absolute coordinate values and assigns the remaining weight to zero. The linear map therefore takes the radius-k ball onto kCₙ. Over a sum-zero d, scaling its constant translates by −1/n gives all preimages. The zero dilation is the singleton at zero. Here k is any natural, including zero, and the assumption n > 0 supplies the nonzero divisor and nonempty index set."))),
                DescribeRole.Theorem))));

    private static Formula MembershipFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var d = F.Id("d");
        var t = F.Id("t");
        var i = F.Id("i");
        var h = Sub(F.Id("H"), n);
        var c = Sub(F.Id("C"), n);
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var residues = Sub(Seq(Mathbb, Grp(F.Id("Z"))), n);
        return Disp(Seq(Forall, Sp, n, Comma, k, Sp, InMacro, Sp, naturals, Comma, Sp,
            D(0), Lt, n, Sp, Implies, Sp, Forall, Sp, d, Sp, InMacro, Sp, h, Comma, Sp,
            d, Sp, InMacro, Sp, k, c, Sp, Iff, Sp, Exists, Sp, t, Sp, InMacro, Sp, reals, Comma, Sp,
            Sub(Sum, Seq(i, Sp, InMacro, Sp, residues)), Sp,
            new Formula.Absolute(Seq(Sub(d, i), Plus, t)), Sp, Le, Sp, n, k));
    }

    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
}
