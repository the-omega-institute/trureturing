using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Spectral;

internal sealed class FillmanLimGapRichClosuresDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Spectral/FillmanLimGapRichClosures.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/fillmanlim2026gaprich");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gap-rich alphabets fail closure under union, sum, and ordered product.",
        H("FillmanLimGapRichClosures"),
        Blocks(
            Entry("fl-fillmanlimgaprichclosures-0", "claim", "Question 2: the three universal assertions",
                Equal(V("claim"), ClaimBody()), AssessedProvenance.FromLiterature(Source),
                "Page 20, Section 6, Question 2: “If X₁, X₂ ⊆ ℝᵏ and X₃ ⊆ ℝˡ are gap-rich, are any of the following sets X₁ ∪ X₂, X₁ + X₂, and X₁ × X₃ gap-rich?” Positive dimensions are natural numbers greater than zero. The union and sum clauses quantify over two subsets of the same Euclidean space. The Cartesian clause uses ordered coordinate concatenation. The three assertions are alternatives, represented by their disjunction.", DescribeRole.Definition),
            Entry("fl-fillmanlimgaprichclosures-1", "result", "All three closure assertions fail",
                Seq(Neg, Sp, Parenthesized(ClaimBody())), AssessedProvenance.FromRepo(Source),
                "The input alphabets have empty exceptional set. Small variations inside a vertical component yield a hyperbolic relative transfer and then a hyperbolic positive word. Locally isolated output components force transfers minus J, minus the identity, or alternating H and minus its adjugate. Their obstruction energies form a nondiscrete set. The witnesses use dimensions three for sums and five for the two union or product factors.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("op-fl2609q2"), ResolutionKind.Refuted)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ClaimBody() =>
        Or(All("k", Nat(), Imp(Less(D(0), V("k")), All("Xone", Sets(Space(V("k"))), All("Xtwo", Sets(Space(V("k"))), Imp(Call("GapRich", V("Xone")), Imp(Call("GapRich", V("Xtwo")), Call("GapRich", Seq(V("Xone"), Sp, Cup, Sp, V("Xtwo"))))))))), Or(All("k", Nat(), Imp(Less(D(0), V("k")), All("Xone", Sets(Space(V("k"))), All("Xtwo", Sets(Space(V("k"))), Imp(Call("GapRich", V("Xone")), Imp(Call("GapRich", V("Xtwo")), Call("GapRich", PlusF(V("Xone"), V("Xtwo"))))))))), All("k", Nat(), All("ell", Nat(), Imp(Less(D(0), V("k")), Imp(Less(D(0), V("ell")), All("Xone", Sets(Space(V("k"))), All("Xthree", Sets(Space(V("ell"))), Imp(Call("GapRich", V("Xone")), Imp(Call("GapRich", V("Xthree")), Call("GapRich", Call("cartesianProduct", V("Xone"), V("Xthree")))))))))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(V(name), args);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Nat() => V("Nat");
    private static Formula Real() => V("Real");
    private static Formula Space(Formula k) => Call("EuclideanSpace", Real(), Call("Fin", k));
    private static Formula Sets(Formula x) => Call("Set", x);
    private static Formula PlusF(Formula a, Formula b) => Seq(Parenthesized(a), Plus, Parenthesized(b));
}
