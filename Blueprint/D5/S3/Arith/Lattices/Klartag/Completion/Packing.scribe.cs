using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class PackingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/Packing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One positive packing constant for every natural dimension.",
        H("Packing"),
        Blocks(
            Paragraph(Text("Construction A provides the lattice point-count profile. A stopped Gaussian walk deforms its quadratic form while controlling contact counts, determinant drift and shortfall. A good realization excludes every nonzero lattice point. Transfer to integer coordinates and scaling then fix the volume exactly, with one constant in every dimension and the zero map at n=0.")),
            Node("claim-1", "Bfam", "Bfam",
                "The terminal counting weight is B(m)=140/(m+1)^2. Its dimension dependence balances the contact and drift estimates.", DescribeRole.Definition),
            Node("claim-2", "Bfam_nonneg", "Bfam nonneg",
                "The terminal counting weight is nonnegative in every natural dimension.", DescribeRole.Theorem),
            Node("claim-3", "Kcut", "Kcut",
                "The cut index: one step short of the horizon.", DescribeRole.Definition),
            Node("claim-4", "Kcut_lt", "Kcut lt",
                "Above the dimension threshold the walk horizon is positive, so its predecessor is a strictly earlier cut index.", DescribeRole.Theorem),
            Node("claim-5", "Kcut_succ", "Kcut succ",
                "Above the dimension threshold, adding one to the cut index recovers the full walk horizon.", DescribeRole.Theorem),
            Node("claim-6", "rrAt", "rr At",
                "The shortfall's free parameter rr, chosen so that rr·mAt ≥ (1+c₃)·η with mAt ≥ 1/2.", DescribeRole.Definition),
            Node("claim-7", "epsAt", "eps At",
                "The perturbation allowance is the reciprocal fourth root of the dimension.", DescribeRole.Definition),
            Node("claim-8", "klartag_packing", "klartag packing",
                "There is one positive real constant c such that, for every natural n, a real linear map on Euclidean space of dimension n+1 sends the open unit ball to a set of volume exactly c*n^2. Its points with integer coordinates are exactly zero. The constant is uniform in n, including n=0. Construction A averaging supplies the lattice, the stopped Gaussian matrix walk supplies the determinant bound, and linear transfer followed by homothetic shrinking gives exact volume.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            declaration == "klartag_packing"
                ? StatementSource.FromAuthor(PackingFormula())
                : StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula PackingFormula()
    {
        Formula c = F.Id("c"), n = F.Id("n"), phi = F.Id("phi");
        Formula space = Seq(Mathbb, Grp(F.Id("R")), Caret, Grp(Seq(n, Plus, D(1))));
        Formula image = Call("image", phi, Call("openUnitBall", space));
        return Disp(Seq(
            Exists, Sp, c, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Sp, Lt, Sp, c, Sp, Land, Sp,
            Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Exists, Sp, phi, Colon, Sp, Call("LinearEnd", space), Comma, Sp,
            Call("volume", image), Sp, Eq, Sp, c, Sp, Cdot, Sp, n, Caret, Grp(D(2)),
            Sp, Land, Sp, Call("IntegerPoints", image), Sp, Eq, Sp,
            OpenBrace, D(0), CloseBrace));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
