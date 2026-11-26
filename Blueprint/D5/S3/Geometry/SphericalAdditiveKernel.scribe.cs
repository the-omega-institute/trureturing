using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class SphericalAdditiveKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A radial obstruction to additive kernels in real inner product spaces.",
        H("Spheres in additive subgroups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finrank-le-one-of-sphere-mem"),
                DeclarationHandle.Create("D5/S3/Geometry/SphericalAdditiveKernel.finrank_le_one_of_sphere_mem"),
                H("A sphere and its half-radius obstruction"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let E be a finite-dimensional real inner product space, K an additive subgroup of E, and r a positive real number. Suppose every vector of norm r belongs to K, and every vector of norm r/2 lies outside K. Then the real dimension of E is at most one. No continuity or closedness assumption is imposed on K.")),
                    Paragraph(Text("If E had dimension at least two, choose orthonormal vectors e and f. The vectors u=(r/4)e+(sqrt(15)r/4)f and v=-(r/4)e+(sqrt(15)r/4)f both have norm r. Their difference is (r/2)e and therefore has norm r/2. Additive closure puts this difference in K, contradicting the second assumption.")),
                    Paragraph(Text("For an exponential homomorphism on a commuting linear subspace, its kernel is an additive subgroup. A radial comparison formula can place the radius-r sphere in that kernel and exclude the half-radius sphere. The theorem then bounds the dimension of that particular commuting subspace; the exponential homomorphism and both radial assertions must be established for the application."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula e = F.Id("E"), k = F.Id("K"), r = F.Id("r"), x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        return Disp(Seq(
            Forall, Sp, e, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Comma, Esc,
            OpenBracket, Call("InnerProductSpace", real, e), CloseBracket, Comma, Esc,
            OpenBracket, Call("FiniteDimensional", real, e), CloseBracket, Comma, Esc,
            k, Colon, Sp, Call("AddSubgroup", e), Comma, Esc,
            r, Colon, Sp, real, Comma, Esc,
            D(0), Lt, r, Sp, Land, Sp,
            Open, Forall, Sp, x, Colon, Sp, e, Comma, Esc,
                Call("norm", x), Eq, r, Sp, Rightarrow, Sp, x, InMacro, Sp, k, Close,
            Sp, Land, Sp,
            Open, Forall, Sp, x, Colon, Sp, e, Comma, Esc,
                Call("norm", x), Eq, Seq(Frac, Grp(r), Grp(D(2))), Sp, Rightarrow, Sp,
                Neg, Sp, Open, x, InMacro, Sp, k, Close, Close,
            Sp, Rightarrow, Sp,
            Call("finrank", real, e), Le, Sp, D(1)));
    }
}
