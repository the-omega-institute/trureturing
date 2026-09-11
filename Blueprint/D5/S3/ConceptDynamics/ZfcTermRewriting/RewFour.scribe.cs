using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcTermRewriting;

internal sealed class RewFourDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Foundation =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/foundation2026firstorder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven general lawful syntactic-rewriting identities from the licensed Foundation source.",
        H("RewFour"),
        Blocks(
            Paragraph(Text("This document mirrors the seven retained theorems in the capacity span "
                + "Foundation/Syntax/Predicate/Rew.lean:954-1080 at revision "
                + "30a16ffa93d79d73ab4d02427fa00f50e039bf29. They express identities between "
                + "rewriting operations on an abstract family of formulas.")),
            Paragraph(Text("All seven statements assume a language L, a family S : Nat -> Type, "
                + "LCWQ S, SyntacticRewriting L S S and LawfulSyntacticRewriting L S. "
                + "S(n) has n available bound-variable indices; free variables are labelled by natural "
                + "numbers. S(0) can still contain free variables. A SyntacticTerm(L) has no bound "
                + "variables and may contain natural-number-labelled free variables.")),
            Paragraph(Text("In the formulas, act(w, phi) is the formula action w ▹ phi, "
                + "apply(w, t) is the term action w t, and rewrite(f) is Rew.rewrite f. "
                + "bShift and shiftTerm are Rew.bShift and Rew.shift on terms. "
                + "shift and free are Rewriting.shift and Rewriting.free on formulas. "
                + "fvar(i) is &i. cons(t, g) maps 0 to t and i+1 to g(i); "
                + "compose(g, f) maps i to g(f(i)). subst(phi, t) means phi/[t]. "
                + "cast(phi) means Rewriting.subst phi ![] with source S(0) and target S(1); "
                + "it adds an unused bound-variable slot. The free operation replaces the sole "
                + "available bound variable by &0 and shifts the old free-variable labels.")),
            DescribeEntry(
                "free-rewrite-eq",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.free_rewrite_eq",
                "Freeing the bound slot transports a lifted rewrite",
                FreeRewriteFormula(),
                "Lift each replacement term with bShift before rewriting a formula in S(1). "
                    + "Freeing its bound slot then agrees with first freeing the formula and rewriting "
                    + "with a map that fixes &0 and shifts every original replacement term."),
            DescribeEntry(
                "shift-rewrite-eq",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.shift_rewrite_eq",
                "Shifting a rewritten formula transports the replacement map",
                ShiftRewriteFormula(),
                "For a formula in S(0), shifting after rewriting equals rewriting the shifted formula "
                    + "with &0 prepended to the map of shifted replacement terms."),
            DescribeEntry(
                "rewrite-subst-eq",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_subst_eq",
                "Rewriting a substitution rewrites both the formula and the substituted term",
                RewriteSubstFormula(),
                "For phi in S(1) and t a syntactic term, rewrite phi/[t] by f. The same result is "
                    + "obtained by rewriting phi with bShift composed with f, and then substituting "
                    + "the term produced by rewriting t with f."),
            DescribeEntry(
                "free-subst-nil",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.free_subst_nil",
                "Freeing an unused bound slot shifts the free variables",
                FreeSubstNilFormula(),
                "The cast from S(0) to S(1) introduces no occurrence of its new bound variable. "
                    + "Applying free to that cast therefore has exactly the effect of shift."),
            DescribeEntry(
                "rewrite-subst-nil",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_subst_nil",
                "A lifted rewrite commutes with adding an unused bound slot",
                RewriteSubstNilFormula(),
                "Rewriting cast(phi) with bShift composed with f agrees with casting the result "
                    + "of rewriting phi with f."),
            DescribeEntry(
                "cast-subst-eq",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.cast_subst_eq",
                "Substituting into an unused bound slot recovers the original formula",
                CastSubstFormula(),
                "For every syntactic term t, substituting t into cast(phi) returns phi. "
                    + "The cast has no occurrence of the added bound variable to replace."),
            DescribeEntry(
                "rewrite-free-eq-subst",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.rewrite_free_eq_subst",
                "Substitution can be expressed by freeing and then rewriting",
                RewriteFreeFormula(),
                "After freeing phi, send &0 to t and each &(i+1) back to &i. "
                    + "This rewrite agrees with directly substituting t for the bound slot in phi."),
            Paragraph(Text("Each declaration retains its upstream name, hypotheses and proof body. "
                + "The source map, modification notices, Apache-2.0 license and retirement condition "
                + "are in Library/ConceptDynamics/foundation2026firstorder.md.")))));

    private static DocumentBlock DescribeEntry(
        string id, string handle, string title, Formula formula, string narrative) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(handle),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Foundation),
            Blocks(Paragraph(Text(narrative))),
            DescribeRole.Lemma);

    private static Formula TermType() => Call("SyntacticTerm", F.Id("L"));

    private static Formula MapBinder() => Seq(
        F.Id("f"), Colon, Sp,
        new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("N"))), TermType()));

    private static Formula TermBinder() => Seq(F.Id("t"), Colon, Sp, TermType());

    private static Formula FormulaBinder(byte n) => Seq(
        F.Id("phi"), Colon, Sp, Call("S", D(n)));

    private static Formula LiftedMap() => Call("compose", F.Id("bShift"), F.Id("f"));

    private static Formula ShiftedMap() => Call(
        "cons", Call("fvar", D(0)), Call("compose", F.Id("shiftTerm"), F.Id("f")));

    private static Formula Act(Formula map, Formula phi) => Call("act", Call("rewrite", map), phi);

    private static Formula FreeRewriteFormula() => Disp(Seq(
        Forall, Sp, MapBinder(), Comma, Sp, FormulaBinder(1), Comma, Sp,
        Call("free", Act(LiftedMap(), F.Id("phi"))), Sp, Eq, Sp,
        Act(ShiftedMap(), Call("free", F.Id("phi"))), Dot));

    private static Formula ShiftRewriteFormula() => Disp(Seq(
        Forall, Sp, MapBinder(), Comma, Sp, FormulaBinder(0), Comma, Sp,
        Call("shift", Act(F.Id("f"), F.Id("phi"))), Sp, Eq, Sp,
        Act(ShiftedMap(), Call("shift", F.Id("phi"))), Dot));

    private static Formula RewriteSubstFormula() => Disp(Seq(
        Forall, Sp, MapBinder(), Comma, Sp, TermBinder(), Comma, Sp, FormulaBinder(1), Comma, Sp,
        Act(F.Id("f"), Call("subst", F.Id("phi"), F.Id("t"))), Sp, Eq, Sp,
        Call("subst", Act(LiftedMap(), F.Id("phi")),
            Call("apply", Call("rewrite", F.Id("f")), F.Id("t"))), Dot));

    private static Formula FreeSubstNilFormula() => Disp(Seq(
        Forall, Sp, FormulaBinder(0), Comma, Sp,
        Call("free", Call("cast", F.Id("phi"))), Sp, Eq, Sp,
        Call("shift", F.Id("phi")), Dot));

    private static Formula RewriteSubstNilFormula() => Disp(Seq(
        Forall, Sp, MapBinder(), Comma, Sp, FormulaBinder(0), Comma, Sp,
        Act(LiftedMap(), Call("cast", F.Id("phi"))), Sp, Eq, Sp,
        Call("cast", Act(F.Id("f"), F.Id("phi"))), Dot));

    private static Formula CastSubstFormula() => Disp(Seq(
        Forall, Sp, TermBinder(), Comma, Sp, FormulaBinder(0), Comma, Sp,
        Call("subst", Call("cast", F.Id("phi")), F.Id("t")), Sp, Eq, Sp, F.Id("phi"), Dot));

    private static Formula RewriteFreeFormula() => Disp(Seq(
        Forall, Sp, TermBinder(), Comma, Sp, FormulaBinder(1), Comma, Sp,
        Act(Call("cons", F.Id("t"), F.Id("fvar")), Call("free", F.Id("phi"))), Sp, Eq, Sp,
        Call("subst", F.Id("phi"), F.Id("t")), Dot));
}
