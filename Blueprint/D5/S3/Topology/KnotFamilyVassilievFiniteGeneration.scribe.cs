using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class KnotFamilyVassilievFiniteGenerationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Topology/KnotFamilyVassilievFiniteGeneration";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Topology/laninasleptsov2026vassilievfamilies");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every family of rational univariate polynomials has a finite subfamily generating the same algebra.",
        H("Finite generation for one-parameter polynomial invariants"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("A finite generating subfamily"),
                StatementSource.FromAuthor(Disp(Equal(
                    Typed(Local("claim"), Qualified("Prop")), Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The family p is indexed by an arbitrary type ι and consists of polynomials over the rational numbers. "
                        + "The assertion asks for a finite set s of indices whose polynomial values generate the same rational subalgebra as the entire family. "
                        + "The expression (s : Set ι) explicitly regards the finite set as a set before taking its image under p. "
                        + "Lanina–Sleptsov describe rational-valued invariants and their algebra in main.tex, lines 350–356, "
                        + "write the one-parameter restrictions as rational polynomials in lines 1114–1117, "
                        + "and ask for finite generation in lines 165 and 1166. "
                        + "Taking p to be these polynomial restrictions gives the algebraic assertion. "
                        + "Generation is ordinary algebra generation: the twist-knot discussion in line 1228 allows higher-order invariants to be polynomials in the second invariant. "
                        + "There is no requirement that the generators preserve the order filtration."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subalgebra-fg"),
                DeclarationHandle.Create(Module + ".subalgebra_fg"),
                H("Subalgebras of a polynomial ring in one variable"),
                StatementSource.FromAuthor(Disp(SubalgebraFormula())),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/HomologicalAlgebra/artintate1951finiteringextensions")),
                Blocks(Paragraph(Text(
                    "For every field k, each k-subalgebra a of the polynomial ring k[X] is finitely generated as a k-algebra. "
                        + "Subalgebra.FG means that a finite set of polynomials generates a as a subalgebra. "
                        + "This is the standard finiteness fact, proved here from the integrality of X over k[f] for a nonconstant polynomial f and the Artin–Tate lemma. "
                        + "For a containing f, the same monic polynomial proves integrality over a; when a contains only constants it is the scalar subalgebra."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Finite generation by members of the given family"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First consider an arbitrary k-subalgebra a of k[X]. "
                            + "If every f in a has natural degree zero, each is the constant polynomial with value its zeroth coefficient. "
                            + "Thus a is contained in the scalar subalgebra; the reverse inclusion holds for every k-subalgebra. "
                            + "Equality with the scalar subalgebra gives finite generation by the empty set.")),
                    Paragraph(Text(
                        "Otherwise choose f in a of positive natural degree and let c be its nonzero leading coefficient. "
                            + "The polynomial q = C(c⁻¹)f is monic and still has positive natural degree. "
                            + "Map its coefficients along the scalar homomorphism from k to a. "
                            + "The resulting polynomial over a remains monic of positive degree, and its evaluation at X is the image under a → k[X] of the element q of a, since a contains both f and the scalar C(c⁻¹). "
                            + "This evaluated value is integral over a. "
                            + "The monic evaluation criterion therefore makes X integral over a; equivalently, subtracting that value from the constant coefficient gives a monic polynomial vanishing at X.")),
                    Paragraph(Text(
                        "The a-subalgebra generated by X is all of k[X]: after restricting scalars to k, it contains X, which generates k[X] over k. "
                            + "Since X is integral, the subalgebra it generates is a finite a-module, so k[X] is a finite a-module. "
                            + "Apply the Artin–Tate lemma to the tower k → a → k[X], using that the field k is Noetherian, that k[X] is a finitely generated k-algebra, and that the inclusion of a is injective. "
                            + "It follows that a is a finitely generated k-algebra. "
                            + "The preceding two cases prove the general subalgebra finiteness statement.")),
                    Paragraph(Text(
                        "Next let p be a polynomial family. An induction on membership in the algebra generated by its range shows that every element belongs to the algebra generated by a finite subfamily. "
                            + "An original value p(i) uses the singleton index set containing i, and a scalar uses the empty index set. "
                            + "For a sum or product, take the union of the two finite index sets and use monotonicity of generated subalgebras.")),
                    Paragraph(Text(
                        "Choose a finite set t of polynomial generators for the algebra generated by the range of p. "
                            + "For each x in t choose a finite index set s(x) whose values generate a subalgebra containing x. "
                            + "Take the finite union of s(x) over x in t. Its polynomial values lie in the range of p, giving one inclusion of generated algebras. "
                            + "Conversely, every generator x in t belongs to the algebra generated by that union, giving the other inclusion. "
                            + "Finally specialize to k equal to the rational field and apply the general subalgebra finiteness statement to the algebra generated by the range of p. "
                            + "The resulting finite set of indices proves the assertion for every ι and p."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lanina-sleptsov-2026-vassiliev-one-parameter-finite-generation"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimFormula() => All("ι", Qualified("Type"),
        All("p", Arrow(Iota, PolynomialOver(Rationals())),
            Some("s", At(Qualified("Finset"), Iota), Equal(
                At(Qualified("Algebra", "adjoin"), Rationals(),
                    At(Qualified("Set", "image"), X("p"), Typed(X("s"), At(Qualified("Set"), Iota)))),
                At(Qualified("Algebra", "adjoin"), Rationals(),
                    At(Qualified("Set", "range"), X("p")))))));

    private static Formula SubalgebraFormula() => All("k", Seq(Qualified("Type"), Star),
        Seq(OpenBracket, At(Qualified("Field"), X("k")), CloseBracket, Comma, Sp,
            All("a", At(Qualified("Subalgebra"), X("k"), PolynomialOver(X("k"))),
                At(Qualified("Subalgebra", "FG"), X("a")))));

    private static Formula X(string name) => name == "ι" ? Iota : F.Id(name);
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Topology", "KnotFamilyVassilievFiniteGeneration", name);
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula PolynomialOver(Formula k) => At(Qualified("Polynomial"), k);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
}
