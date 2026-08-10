using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class ClosureUndecidableDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Rice =
        LibraryNoteRef.Create("D5/L/Diagonal/rice1953classes");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Computability/ClosureUndecidable",
                "No computable total reading decides a nontrivial behavior-level closure predicate."),
            H("Closure Readings Are Unreachable"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("no-same-layer-reading-decides-closure"),
                    H("No same-layer reading decides closure"),
                    LeanTheorem(
                        "D5/S0/Computability/ClosureUndecidable.closure_reading_unreachable"),
                    Disp(Seq(
                        Neg, Exists, Sp, Esc, F.Text, Grp(Seq(
                            F.Id("computable"), Sp, F.Id("total"))), Sp, F.Id("C"),
                        Comma, Sp, Forall, Sp, F.Id("c"), Comma, Sp,
                        F.Id("C"), Open, F.Id("c"), Close, Sp, Eq, Sp, D(1),
                        Sp, Iff, Sp, F.Id("c"), InMacro, Sp,
                        Operatorname, Grp(F.Id("Closed")), Dot)),
                    DescribeProvenance.LiteratureAttested(Rice),
                    Blocks(
                        Paragraph(Text(
                            "Let a closure predicate on partial recursive codes be taken at "
                            + "the same layer as the objects it judges: whether a code counts "
                            + "as closed depends only on the behavior the code describes, so "
                            + "codes of equal evaluation are equi-closed. If the predicate is "
                            + "nontrivial - some code is closed and some code is not - then no "
                            + "total computable reading decides it. A reading that lives in "
                            + "the same kernel as its objects can therefore never certify "
                            + "closure across the board: the deciding hand would itself be a "
                            + "code, and the fixed-point diagonal builds a code that consults "
                            + "the reading on itself and enacts the opposite verdict, "
                            + "contradicting either answer.")),
                        Paragraph(Text(
                            "The library was searched before proving: the pinned Mathlib "
                            + "already holds Rice's theorem in exactly this shape, as an "
                            + "equivalence between decidability of a behavior-respecting code "
                            + "predicate and the triviality of that predicate, proved from "
                            + "the second recursion theorem. The Lean declaration is a "
                            + "declared thin honest wrapper: it applies the upstream "
                            + "equivalence and discharges the two trivial branches against "
                            + "the nontriviality witnesses. The scope is honest - the "
                            + "statement formalizes the same-layer clause of the source "
                            + "theorem; its cross-layer relativization is a separate "
                            + "frontier item.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("the-empty-ledger-reading-is-unreachable"),
                    H("The empty-ledger reading is unreachable"),
                    LeanTheorem(
                        "D5/S0/Computability/ClosureUndecidable.empty_ledger_reading_unreachable"),
                    Disp(Seq(
                        Neg, Exists, Sp, Esc, F.Text, Grp(Seq(
                            F.Id("computable"), Sp, F.Id("total"))), Sp, F.Id("C"),
                        Comma, Sp, Forall, Sp, F.Id("c"), Comma, Sp,
                        F.Id("C"), Open, F.Id("c"), Close, Sp, Eq, Sp, D(1),
                        Sp, Iff, Sp,
                        Operatorname, Grp(F.Id("eval")), Open, F.Id("c"), Close,
                        Sp, Eq, Sp, Varnothing, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "The wrapper is instantiated at the concrete closure predicate "
                            + "of the source proof: the empty-ledger behavior, a code whose "
                            + "described program certifies nothing because its evaluation is "
                            + "everywhere undefined. That predicate respects behavior by "
                            + "construction, the everywhere-undefined behavior has a code, "
                            + "and the total identity behavior supplies a code outside the "
                            + "class - so the predicate is nontrivial and no total computable "
                            + "reading decides it. The instantiation keeps the wrapper "
                            + "honest: the primary theorem is quantified over all same-layer "
                            + "closure predicates, and this witness exercises it on the one "
                            + "the diagonal argument toggles against. The statement is "
                            + "assembled in the repository from the wrapped theorem, so it "
                            + "is conservatively recorded as repository-derived.")))
                ))));
}
