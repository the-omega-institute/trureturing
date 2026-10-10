using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.RenyiSufficiency;

internal sealed class RenyiSufficiencyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/galke2023renyisufficiency");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.",
        H("RenyiSufficiencyRefutation"),
        Blocks(
            Node("weighted-charpoly-eq", "weighted charpoly eq", "weighted_charpoly_eq",
                Disp(All("e", Seq(Mathbb, Grp(F.Id("C"))), All("d", Seq(Call("Fin"), Sp, D(5), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C")))), Seq(Parenthesized(Seq(Call("weightedRho"), Sp, Call("false"), Sp, F.Id("e"), Sp, F.Id("d"))), Sp, Seq(Dot, Call("charpoly")), Sp, Eq, Sp, Parenthesized(Seq(Call("weightedRho"), Sp, Call("true"), Sp, F.Id("e"), Sp, F.Id("d"))), Sp, Seq(Dot, Call("charpoly")))))),
                "The two orientations of each triangle cancel in the principal minors. Multiplication on both sides by an arbitrary diagonal matrix retains equality of the characteristic polynomials.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("rho-isdensity", "rho isDensity", "rho_isDensity",
                Disp(All("minus", Call("Bool"), Seq(Call("IsDensity"), Sp, Parenthesized(Seq(Call("rho"), Sp, F.Id("minus"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0)))))))),
                "The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("sigma-isdensity", "sigma isDensity", "sigma_isDensity",
                Disp(Seq(Call("IsDensity"), Sp, Call("sigma"))),
                "The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("dminfinite-bouquet", "DminFinite bouquet", "DminFinite_bouquet",
                Disp(All("minus", Call("Bool"), All("alpha", Seq(Mathbb, Grp(F.Id("R"))), Seq(Call("DminFinite"), Sp, Parenthesized(Seq(Call("rho"), Sp, F.Id("minus"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))))), Sp, Call("sigma"), Sp, F.Id("alpha"))))),
                "The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("checkpoint-profiles", "checkpoint profiles", "checkpoint_profiles",
                Disp(All("alpha", Seq(Mathbb, Grp(F.Id("R"))), Imp(Seq(F.Id("alpha"), Sp, InMacro, Sp, Seq(Call("Set"), Dot, Call("Ioo")), Sp, Parenthesized(Seq(D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, D(3)), Seq(Parenthesized(Seq(Call("Dmin"), Sp, Parenthesized(Seq(Call("rho"), Sp, Call("false"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))))), Sp, Call("sigma"), Sp, F.Id("alpha"), Sp, Eq, Sp, Call("Dmin"), Sp, Parenthesized(Seq(Call("rho"), Sp, Call("true"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))))), Sp, Call("sigma"), Sp, F.Id("alpha"))), Sp, Land, Sp, Parenthesized(Seq(Call("DminFinite"), Sp, Parenthesized(Seq(Call("rho"), Sp, Call("false"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))))), Sp, Call("sigma"), Sp, F.Id("alpha"))), Sp, Land, Sp, Parenthesized(Seq(Call("DminFinite"), Sp, Parenthesized(Seq(Call("rho"), Sp, Call("true"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))))), Sp, Call("sigma"), Sp, F.Id("alpha"))))))),
                "The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("claim", "claim", "claim",
                Disp(Seq(Call("claim"), Sp, Eq, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("rho1"), Sp, F.Id("sigma1"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("rho2"), Sp, F.Id("sigma2"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("m"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("m"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Call("IsDensity"), Sp, F.Id("rho1"), Sp, To, Sp, Call("IsDensity"), Sp, F.Id("sigma1"), Sp, To, Sp, Call("IsDensity"), Sp, F.Id("rho2"), Sp, To, Sp, Call("IsDensity"), Sp, F.Id("sigma2"), Sp, To, Sp, Forall, Sp, F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Comma, Sp, D(1), Sp, Slash, Sp, D(2), Sp, Leq, Sp, F.Id("a"), Sp, To, Sp, F.Id("a"), Sp, Lt, Sp, F.Id("b"), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("alpha"), Sp, InMacro, Sp, Seq(Call("Set"), Dot, Call("Ioo")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, Comma, Sp, Parenthesized(Seq(Call("DminFinite"), Sp, F.Id("rho1"), Sp, F.Id("sigma1"), Sp, F.Id("alpha"))), Sp, Land, Sp, Parenthesized(Seq(Call("DminFinite"), Sp, F.Id("rho2"), Sp, F.Id("sigma2"), Sp, F.Id("alpha"))))), Sp, To, Sp, Parenthesized(Seq(Call("Interconvertible"), Sp, F.Id("rho1"), Sp, F.Id("sigma1"), Sp, F.Id("rho2"), Sp, F.Id("sigma2"), Sp, Iff, Sp, Forall, Sp, F.Id("alpha"), Sp, InMacro, Sp, Seq(Call("Set"), Dot, Call("Ioo")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, Comma, Sp, Call("Dmin"), Sp, F.Id("rho1"), Sp, F.Id("sigma1"), Sp, F.Id("alpha"), Sp, Eq, Sp, Call("Dmin"), Sp, F.Id("rho2"), Sp, F.Id("sigma2"), Sp, F.Id("alpha"))))))),
                "Galke, van Luijk and Wilming, Conjecture 22, Section 3.3, arXiv:2304.12989v6, p. 17: “Let (ρ₁, σ₁) and (ρ₂, σ₂) be pairs of density operators on quantum system S₁ and S₂. Let (a, b), ½ ≤ a < b, be any interval on which the minimal quantum Rényi divergences of both dichotomies are finite. Then the dichotomies are interconvertible via positive, trace-preserving maps if and only if they have the same minimal quantum Rényi divergences on this interval, i.e., (ρ₁, σ₁) ↔ (ρ₂, σ₂) ⇐⇒ Dᵐⁱⁿ_α(ρ₁, σ₁) = Dᵐⁱⁿ_α(ρ₂, σ₂) < ∞ ∀α ∈ (a, b).” The dimensions n and m range over Nat; the states are complex Fin-indexed matrices. IsDensity is the existing predicate asserting positive semidefiniteness and trace one. Dmin and DminFinite implement Appendix E with support inclusion also at alpha=1.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", "result",
                Disp(Seq(Neg, Sp, Call("claim"))),
                "At dimension five, epsilon=1/1000 and interval (2,3), the two bouquet dichotomies have equal finite minimal Rényi profiles. Their two-triangle gain changes sign, which precludes both sigma-preserving conjugation orientations and therefore positive trace-preserving interconversion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name)))
            : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Parenthesized(premise), Sp, To, Sp, body);
}
