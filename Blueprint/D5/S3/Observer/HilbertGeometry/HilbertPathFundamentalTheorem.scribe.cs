using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HilbertGeometry;

internal sealed class HilbertPathFundamentalTheoremDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual derivatives and pointwise Bochner reconstruction for absolutely continuous Hilbert paths. "
        + "In both statements, u is an arbitrary universe level.",
        H("Hilbert Path Fundamental Theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hilbert-ac-actual-derivative"),
                DeclarationHandle.Create(Prefix + "absolutely_continuous_interval_ae_hasDerivAt"),
                H("Actual derivatives almost everywhere"),
                StatementSource.FromAuthor(DerivativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an arbitrary complete real Hilbert space H and every absolutely continuous "
                    + "path f, HasDerivAt holds with the totalized derivative at Lebesgue almost every "
                    + "point of the unordered closed interval. This implies actual differentiability; "
                    + "it is not inferred from totalization. No dimension or ambient separability "
                    + "hypothesis is imposed. Complex Hilbert spaces are included by restricting "
                    + "their scalar structure to the real numbers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hilbert-ac-pointwise-bochner-reconstruction"),
                DeclarationHandle.Create(Prefix + "absolutely_continuous_interval_integral_deriv_eq_sub"),
                H("Pointwise Bochner reconstruction"),
                StatementSource.FromAuthor(ReconstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The oriented Bochner interval integral with respect to Lebesgue measure "
                    + "reconstructs f at every point t of the interval, including its endpoints. "
                    + "The proof first passes to the separable closed span of the interval image. "
                    + "Scalar coordinate derivatives satisfy finite square-sum bounds controlled "
                    + "by signed variation. Their orthogonal series supplies a measurable, integrable "
                    + "Hilbert velocity. Coordinate integral exchange, scalar FTC and coordinate "
                    + "separation give pointwise reconstruction; differentiation of that Bochner "
                    + "primitive identifies the velocity with the actual derivative.")),
                    Paragraph(Text(
                    "This is the analytic prerequisite for qdo-v1 theorem 36.26 and the named "
                    + "consumer absolutely_continuous_subspace_action_minimum_unique. The extended "
                    + "quadratic action, lower bound, affine attainment and pointwise uniqueness "
                    + "remain downstream. Absolute continuity alone does not imply finite "
                    + "quadratic energy. The private countable-basis helpers are a minimal "
                    + "Apache-2.0 source port from Kitware's immutable revision "
                    + "ef157afc71c3866cb608111ef61462516330ef56; their license and notice trail "
                    + "are retained in the Lean source."))),
                DescribeRole.Theorem))));

    private static Formula DerivativeFormula()
    {
        Formula t = F.Id("t");
        Formula path = F.Id("f");
        return WithContext(Call("AlmostEverywhere", F.Id("volume"),
            Seq(LambdaLower, Sp, t, Colon, Sp, F.Id("Real"), Sp, Mapsto, Sp,
                t, Sp, InMacro, Sp, Call("uIcc", F.Id("a"), F.Id("b")),
                Sp, Implies, Sp,
                Call("HasDerivAt", path, Call("deriv", path, t), t))));
    }

    private static Formula ReconstructionFormula()
    {
        Formula t = F.Id("t");
        Formula path = F.Id("f");
        Formula a = F.Id("a");
        return WithContext(Seq(
            Forall, Sp, t, Colon, Sp, F.Id("Real"), Comma, Sp,
            t, Sp, InMacro, Sp, Call("uIcc", a, F.Id("b")), Sp, Implies, Sp,
            Call("intervalIntegral", Call("deriv", path), a, t, F.Id("volume")),
            Sp, Eq, Sp, Call("f", t), Sp, Minus, Sp, Call("f", a)));
    }

    private static Formula WithContext(Formula conclusion)
    {
        Formula space = F.Id("H");
        Formula real = F.Id("Real");
        return Disp(Seq(
            Forall, Sp, space, Colon, Sp, Operatorname, Grp(F.Id("Type")), Underscore, Grp(F.Id("u")), Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", space), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", real, space), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompleteSpace", space), CloseBracket, Comma,
            RowBreak, Grp(),
            Forall, Sp, F.Id("f"), Colon, Sp, real, Sp, To, Sp, space, Comma, Sp,
            Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Colon, Sp, real, Comma, Sp,
            Call("AbsolutelyContinuousOnInterval", F.Id("f"), F.Id("a"), F.Id("b")),
            Sp, Implies, Sp, conclusion, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
