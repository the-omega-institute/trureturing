using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class HircheArimotoCombiningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/hirche2020renyibounds");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hirche's binary Arimoto information combining conjecture holds with threshold three halves on the full closed coordinate range.",
        H("Hirche's Arimoto information combining conjecture"), Blocks(
            Paragraph(Text("C. Hirche, Rényi Bounds on Information Combining, ISIT 2020, arXiv:2004.14408v1, "
                + "§IV-A, Conjecture IV.6: “There exists a value 1 < α̂ < 1.5783, such that "
                + "k_α^A(k_α^A⁻¹(x) ∗ k_α^A⁻¹(y)) (47) is convex for 0 < α < 1 and concave for 1 < α ≤ α̂.” "
                + "Equation (23) defines K_α^A(X|Y) = e^{((1−α)/α) H_α^A(X|Y)}. "
                + "For binary X ~ {p, 1−p}, k_α^A(p) = K_α^A(X) = (p^α + (1−p)^α)^{1/α}; "
                + "write k for this coordinate. The assertion concerns each coordinate separately. "
                + "All powers in k and delta use Real.rpow. "
                + "At alpha=1, k is constant and the inverse branch does not exist; this order is excluded.")),
            Paragraph(Text("O. Rioul and J. Béguinot, The role of Mrs. Gerber's Lemma for evaluating the information "
                + "leakage of secret sharing schemes, Barron Festschrift (Springer), HAL hal-05074668v1, "
                + "§4, p. 20, Proposition 1 and Remark 6, give the prior numerical statement of the threshold α̂ = 3/2. "
                + "Their support is a numerical sign plot produced with SageMath (Figure 3); no proof is given there. See "),
                Ref("D5/L/Entropy/rioulbeguinot2025informationcombining"), Text(".")),
            Node("k", "Binary Arimoto coordinate", All("alpha", All("p",
                Equal(Call("k", N("alpha"), N("p")), Pow(Add(Pow(N("p"), N("alpha")),
                    Pow(Subtract(D(1), N("p")), N("alpha"))), Frac(D(1), N("alpha")))))),
                DescribeRole.Definition, "The probability domain of the inverse branch is [0,1/2]."),
            Node("delta", "Coordinate endpoint", All("alpha", Equal(Call("delta", N("alpha")),
                Pow(D(2), Frac(Subtract(D(1), N("alpha")), N("alpha"))))), DescribeRole.Definition,
                "The half-probability value of k is delta, and its zero-probability value is one."),
            Node("I", "Closed coordinate range", All("alpha", Equal(Call("I", N("alpha")),
                Call("Icc", Call("min", D(1), Call("delta", N("alpha"))),
                    Call("max", D(1), Call("delta", N("alpha")))))), DescribeRole.Definition,
                "For every positive alpha different from one, k is a continuous bijection from [0,1/2] onto this interval."),
            Node("kInv", "Specified probability inverse", All("alpha", All("x",
                Equal(Call("kInv", N("alpha"), N("x")), Call("invFunOn", Call("k", N("alpha")),
                    Call("Icc", D(0), Frac(D(1), D(2))), N("x"))))), DescribeRole.Definition,
                "Function.invFunOn specifies the branch. On I(alpha) it equals the existing Cachin entropy inverse "
                    + "at alpha log(x)/(1-alpha); this proves continuity using that inverse."),
            Node("star", "Binary convolution", All("a", All("b", Equal(Call("star", N("a"), N("b")),
                Subtract(Add(N("a"), N("b")), Multiply(Multiply(D(2), N("a")), N("b")))))),
                DescribeRole.Definition, "This is the shared binary convolution bconv."),
            Node("G", "Arimoto combining map", All("alpha", All("x", All("y",
                Equal(Call("G", N("alpha"), N("x"), N("y")), Call("k", N("alpha"),
                    Call("star", Call("kInv", N("alpha"), N("x")),
                        Call("kInv", N("alpha"), N("y")))))))), DescribeRole.Definition,
                "The two inputs use the same specified inverse branch."),
            Node("claim", "Complete threshold claim", Equal(N("claim"), ClaimBody()), DescribeRole.Definition,
                "The claim quantifies over all real orders in both ranges and every y in the closed range I(alpha)."),
            Node("result", "Conjecture IV.6 with witness three halves", ClaimBody(), DescribeRole.Theorem,
                "The witness is alphaHat=3/2, strictly between one and 15783/10000. "
                    + "The result proves closed-interval separate convexity for all 0<alpha<1 "
                    + "and separate concavity for all 1<alpha≤3/2.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hirche-2020-arimoto-information-combining-convexity"), ResolutionKind.Proved)),
            Paragraph(Text("Put psi(t)=k(alpha,(1-t)/2), c=(1-alpha)/alpha, and let f be the positive Cachin bias slope. "
                + "Then psi=exp(c h), psi'=-c psi f, and the existing derivative certificate f'=f F/t gives "
                + "the Arimoto elasticity E=F-c t f=A/(1+tT). The shared identity bconv_bias gives "
                + "G(psi(t),psi(v))=psi(vt). Identifying T with tanh((alpha-1)s) at t=tanh(s), "
                + "uniqueness of derivatives identifies E with the hyperbolic certificate. "
                + "Thus E increases throughout both order ranges.")),
            Paragraph(Text("For fixed 0<v<1, the derivative ratio R(t)=v psi'(vt)/psi'(t) satisfies "
                + "R'=v psi'(vt)(E(vt)-E(t))/(t psi'(t))≤0. The prefactor is positive because "
                + "both slopes have the same nonzero sign. Below order one the inverse bias decreases, "
                + "so the transported derivative increases and the slice is convex. Above one it increases, "
                + "so the transported derivative decreases and the slice is concave. Continuity on the closed range "
                + "extends these inequalities to its endpoints. At v=0 the slice is constant, and at v=1 it is the identity. "
                + "No endpoint inverse derivative is assumed.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hirche-arimoto-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            (name == "result" ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source)),
            Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);
    private static Formula N(string x) => F.Id(x);
    private static Formula RealType() => Seq(Mathbb, Grp(N("R")));
    private static Formula All(string x, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), RealType(), body);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Slice(string shape) => All("y", Imp(
        new Formula.Relation(N("y"), FormulaRelationOperator.MemberOf, Call("I", N("alpha"))),
        Call(shape, RealType(), Call("I", N("alpha")),
            Seq(N("x"), Sp, Mapsto, Sp, Call("G", N("alpha"), N("x"), N("y"))))));
    private static Formula ClaimBody() => Seq(Exists, Sp, N("alphaHat"), Colon, RealType(), Comma,
        And(Lt(D(1), N("alphaHat")), And(Lt(N("alphaHat"), Frac(D(1,5,7,8,3), D(1,0,0,0,0))),
            And(All("alpha", Imp(Lt(D(0), N("alpha")), Imp(Lt(N("alpha"), D(1)), Slice("ConvexOn")))),
                All("alpha", Imp(Lt(D(1), N("alpha")), Imp(Le(N("alpha"), N("alphaHat")), Slice("ConcaveOn"))))))));
}
