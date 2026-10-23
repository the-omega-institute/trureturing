using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class StrictAnchoredBoundaryDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula LeqOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula Statement()
    {
        var alphabet = F.Id("A"); var n = F.Id("n"); var c = F.Id("C");
        var k = F.Id("k"); var d = F.Id("d"); var s = F.Id("s");
        var t = F.Id("t"); var i = F.Id("i"); var f = F.Id("f");
        var b = F.Id("b"); var residual = F.Id("S"); var inst = F.Id("I");
        var x = F.Id("X"); var a = F.Id("a"); var g = F.Id("g"); var h = F.Id("h");
        var words = Call("List", alphabet);
        var states = Seq(words, Sp, Times, Sp, words);
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var typed = Call("typedState", c, k, d);
        var image = Call("image", c, k, d);
        var residuals = Call("residualSet", c, Subtract(k, d));
        Formula Boundary(Formula z) => Call("boundary", c, z);
        Formula Actual(Formula z) => Call("actual", c, z);
        Formula Public(Formula z) => Call("publicType", z);
        var update = All("s", states, All("i", Call("Action", alphabet),
            Imp(Actual(s), Equal(
                Call("mapTypeBoundary", c, Call("step", n, c, s, i)),
                Call("boundaryStep", n, Public(s), Boundary(s), i)))));
        var kernel = All("s", states, All("t", states,
            Imp(And(Actual(s), Actual(t), Equal(Public(s), Public(t))),
                new Formula.Logic(Equal(Call("legal", n, c, s), Call("legal", n, c, t)),
                    FormulaLogicOperator.Iff, Equal(Boundary(s), Boundary(t))))));
        var imageClause = All("b", Seq(Call("Set", words), Sp, Times, Sp, words),
            new Formula.Logic(Call("Member", b, image), FormulaLogicOperator.Iff,
                And(Call("Member", Call("fst", b), residuals),
                    Call("Member", Call("snd", b), Call("pref", Call("fst", b), d)))));
        var count = Some("I", Call("Fintype", residuals), Equal(Call("card", image),
            Call("sum", inst, new Formula.Sequence(Call("card", Call("pref", residual, d)),
                residual, residuals))));
        var represented = new Formula.SetBuilder(At(a, s), s, typed);
        var factorType = Arrow(represented, image);
        Formula FactorLaw(Formula factor) => And(
            All("s", typed, Equal(At(factor, At(a, s)), Boundary(s))),
            Call("Surjective", factor), LeqOf(Call("card", image), Call("card", represented)));
        var minimum = All("X", F.Id("Type"), All("a", Arrow(states, x),
            Imp(Call("Exact", n, c, a), Some("g", factorType, And(FactorLaw(g),
                All("h", factorType, Imp(FactorLaw(h), Equal(h, g))))))));
        var hypotheses = And(Call("Finite", alphabet), Call("Nonempty", alphabet),
            All("f", words, Imp(Call("Member", f, c), Equal(Call("length", f), n))),
            Call("Nonempty", c), LeqOf(d, k), LeqOf(k, n));
        return All("A", F.Id("Type"), All("n", nat, All("C", Call("Set", words),
            All("k", nat, All("d", nat, Imp(hypotheses,
                And(update, kernel, imageClause, count, minimum)))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict supplied append and credit-limited deletion identify the anchored residual boundary of a finite relation.",
        H("Strict Anchored Boundary"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-anchored-specialization"),
            DeclarationHandle.Create("D5/S3/ObserverMemory/StrictAnchoredBoundary.strict_anchored_specialization"),
            H("Strict anchored specialization"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix an arbitrary finite nonempty alphabet A, a natural n, and a nonempty relation C of words of length n. At any admissible public type (k,d), a state is the unique decomposition u=vt with |v|=k-d and |t|=d. The carrier stores this decomposition of the actual controlled prefix, with a completion in the same C; it carries no immutable completed word. The root output is (|v|+|t|,|t|).")),
                Paragraph(Text("The common actions append a and delete a are strict Option transitions. Append requires k<n and an actual completion of vta. With an empty tail it replaces the anchor by va; with tail cw it replaces the anchor by vc and the tail by wa. Delete requires that the tail ends in the supplied a and removes it, leaving the anchor fixed. An empty tail or a mismatching supplied symbol has no edge. Successful labels are the supplied actions, and the public types are (k+1,d) and (k-1,d-1). There is no failure output or enabled-action sensor; deletion can expose a prefix with a different completion in C.")),
                Paragraph(Text("The boundary is (R(v),t), with R(v)={f: vf belongs to C}. The first theorem clause is the exact Option-map equation for public type and boundary. Its explicit boundaryStep gives append guard k<n and a nonempty derivative at ta, the two moving-anchor derivative updates, and the strict delete update (S,wa) to (S,w). These equations apply to every finite action interleaving, with undefined transitions retained as missing edges.")),
                Paragraph(Text("The converse is operational: reverse supplied deletions of z with |z|=|t| are legal exactly when z=t, and end at (v,empty). From there, appending a full-length f is legal exactly when vf belongs to C. These action words separate unequal tails or unequal anchor residuals on actual prefixes.")),
                Paragraph(Text("The image is the actual joint range, exactly pairs (S,t) with S an actual anchor residual at k-d, |t|=d, and a nonempty derivative of S at t. The image is in bijection with the dependent disjoint union of these tail fibers, so N is the sum over distinct actual S of |Pref_d(S)|. This is a joint image, with no independent product assumption.")),
                Paragraph(Text("Exact representations preserve strict domains and successor public types and representation values on actual states. An arbitrary family at public types can be represented in a common tagged carrier; only the image at the chosen type is counted. Equality of exact representation values implies equal legal languages by induction and hence equal boundaries. The realized-image factorization applies to this kernel inclusion. Commutation forces onto-ness and uniqueness, and the finite surjection cardinal theorem gives the lower bound N. The boundary's strict transition equation attains this conditional state capacity.")),
                Paragraph(Text("All hypotheses and quantifiers include n=0, d=0, d=k, k=n, and singleton relations without special exclusions. The count describes internal labels at a supplied public type. Counting multiple public types requires their disjoint union. Binary encodings, when used, are the standard fixed-length finite-capacity encoding of N labels; the theorem assigns no cost to the relation description, transition table, computation, initialization, physical memory or past archive. An accessible extra source record must be part of the represented joint carrier.")),
                Paragraph(Text("In the displayed statement, mapTypeBoundary maps a successful state r to (publicType(r),boundary(C,r)) and preserves none. Subtype arguments denote their underlying states, and actual-image maps use the canonical range inclusions. card is finite cardinality; sum uses the indicated finite enumeration I. The factor equation is the pointwise form of equality between the two canonical range factorizations."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Automata/TypedPartialDFAOOverBase")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization"))]));
}
