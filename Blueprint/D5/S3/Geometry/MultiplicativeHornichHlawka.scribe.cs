using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MultiplicativeHornichHlawkaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/MultiplicativeHornichHlawka.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/marinescuniculescu2024survey");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multiplicative Hornich–Hlawka inequality holds in every real or complex inner product space.",
        H("The multiplicative Hornich–Hlawka inequality"),
        Blocks(
            Paragraph(Text("Marinescu and Niculescu, A survey of the Hornich-Hlawka inequality, arXiv:2407.03278v1, §6, the paragraph applying Theorem 8 to the logarithm: “Applying Theorem 8 to the function f (x) = ln(1 + x) one obtains the multiplicative analog of the inequality (2.1), (1 + |x|)(1 + |y|)(1 + |z|)(1 + |x + y + z|) ≥ (1 + |x + y|)(1 + |y + z|)(1 + |z + x|), for all x, y, z ∈ R. No extension of this remark to the case of inner product spaces is known.”")),
            Entry("multiplicative-claim", "claim", "The inner-product-space claim", Claim(),
                "The scalar type K has RCLike, and E has NormedAddCommGroup and InnerProductSpace K E. Thus the statement covers every real or complex inner product space and every triple x, y, z. It requires neither finite dimension nor completeness. The claim extends the scalar multiplicative inequality in §6 of the survey.",
                DescribeRole.Definition),
            Entry("multiplicative-result", "result", "Proof of the multiplicative inequality", Disp(V("claim")),
                "Set a = ‖x‖, b = ‖y‖, c = ‖z‖, d = ‖x+y+z‖, u = ‖x+y‖, v = ‖y+z‖, w = ‖z+x‖. Ptolemy gives uv ≤ ac+bd, vw ≤ ab+cd, and wu ≤ bc+ad, hence the second elementary symmetric function comparison. The Fréchet identity a²+b²+c²+d² = u²+v²+w², together with these Ptolemy comparisons, gives u+v+w ≤ a+b+c+d. With S = a+b+c+d and R = abc+abd+acd+bcd, the identity R² − (ab+cd)(ac+bd)(bc+ad) = abcd(S² − 2(a²+b²+c²+d²)) gives uvw ≤ R: the four triangle inequalities imply each of a, b, c, d is at most S/2, so the defect is nonnegative. Comparing the linear, quadratic, and cubic terms, together with abcd ≥ 0, proves the product inequality. These steps are established in scalar_inequality; ptolemy_sum, frechet_identity, and norm_triangle_four provide its geometric premises. The underlying real inner product supplied by InnerProductSpace.rclikeToReal also covers complex spaces. Equality classification and extensions to all Hornich–Hlawka normed spaces or all Bernstein functions are not established by this module.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("marinescu-niculescu-2024-multiplicative-hornich-hlawka"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Comma, Sp);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Factor(Formula vector) =>
        Parenthesized(Add(D(1), new Formula.Norm(vector)));

    private static Formula Claim()
    {
        Formula x = V("x"), y = V("y"), z = V("z");
        Formula lhs = Mul(Mul(Factor(Add(x, y)), Factor(Add(y, z))), Factor(Add(z, x)));
        Formula rhs = Mul(Mul(Mul(Factor(x), Factor(y)), Factor(z)), Factor(Add(Add(x, y), z)));
        Formula inequality = new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs);
        Formula vectors = All("x", V("E"), All("y", V("E"), All("z", V("E"), inequality)));
        Formula body = All("K", V("Type"), Seq(
            Instance("RCLike", V("K")),
            All("E", V("Type"), Seq(
                Instance("NormedAddCommGroup", V("E")),
                Instance("InnerProductSpace", V("K"), V("E")), vectors))));
        return Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }
}
