using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class HeibBruschiHiddenCenterRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/heib2026structural");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A hidden central direction refutes Heib–Bruschi Conjecture 80.",
        H("A hidden central direction refutes Heib–Bruschi Conjecture 80"),
        Blocks(
            Node("conjecture-over", "Conjecture 80 over a field", "conjecture80Over", ConjectureFormula(),
                "For each Lie algebra over K and each admissible finite basis b, a nonzero center is required to imply that a proper nonempty subset W of the basis indices has the ideal-graph-property and that the span of b(W) is a solvable Lie ideal. The graph belongs to the given basis: the assertion quantifies over every admissible basis.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 80", "claim", ClaimFormula(),
                "Conjecture 80 of Heib and Bruschi, arXiv:2601.16161v1, §IV.D, p. 46: \"Let g be a finite-dimensional minimal-graph-admissible Lie algebra associated with the minimal graph G(V,E). If g has a non-zero center Z(g), then there exists a proper non-empty subset W⊊V that satisfies the ideal-graph-property and spans a solvable ideal of g.\" The paper's convention \"We denote any field with the symbol 𝔽\" makes this an assertion over every field K.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Conjecture 80 is refuted", "result", ResultFormula(),
                "For any field K, give K⁴ the bracket [u,v]=(b(r+s)−(c+d)q, (c+d)p−a(r+s), aq−bp, 0), where u=(a,b,c,d) and v=(p,q,r,s). The map u↦((a,b,c+d),d) identifies this with the cross-product Lie algebra K³ together with a central copy of K. Its standard basis satisfies [e₁,e₂]=e₃, [e₂,e₃]=e₁, [e₃,e₁]=e₂, [e₁,e₄]=−e₂, [e₂,e₄]=e₁ and [e₃,e₄]=0, so it is admissible, while e₄−e₃ is central and nonzero. Every nonempty vertex subset with the ideal-graph-property contains e₁,e₂,e₃; the only proper one is {e₁,e₂,e₃}. Its span I satisfies [I,I]=I≠0 and is therefore not solvable. These identities hold in every characteristic. Taking K to be the rational numbers contradicts the assertion over every field.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("heib-bruschi-2026-conjecture-80-hidden-center-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula TypeU() => V("Type");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Inst(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Not(Formula body) => Seq(Neg, Sp, body);

    private static Formula ConjectureFormula()
    {
        Formula k = V("K"), l = V("L"), n = V("n"), b = V("b"), w = V("W"), i = V("I");
        Formula fin = Call("Fin", n);
        Formula ideal = Some(i, Call("LieIdeal", k, l),
            And(Equal(Call("toSubmodule", i), Call("span", k, Call("image", b, w))),
                Call("IsSolvable", i)));
        Formula subset = Some(w, Call("Set", fin),
            And(Call("Nonempty", w), And(NotEqual(w, Call("univ")),
                And(Call("IdealGraphProperty", b, w), Parenthesized(ideal)))));
        Formula body = For(l, TypeU(), Inst(Call("LieRing", l), Inst(Call("LieAlgebra", k, l),
            For(n, N(), For(b, Call("Basis", fin, k, l),
                Imp(Call("IsAdmissible", b), Imp(NotEqual(Call("center", k, l), Perp),
                    Parenthesized(subset))))))));
        return Disp(For(k, TypeU(), Inst(Call("Field", k),
            IffOf(Call("conjecture80Over", k), Parenthesized(body)))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = V("K");
        return Disp(IffOf(V("claim"),
            Parenthesized(For(k, TypeU(), Inst(Call("Field", k), Call("conjecture80Over", k))))));
    }

    private static Formula ResultFormula() => Disp(Not(V("claim")));
}
