using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class DisjointStrictRefinementDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Oeis =
        LibraryNoteRef.Create("D5/L/ArithSums/wiseman2025disjoint");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive set admits a nontrivial disjoint strict partition family "
            + "exactly when one member is a sum of distinct positive nonmembers.",
        H("Disjoint Strict Refinement: A384350 and A384318"),
        Blocks(
            Paragraph(Text(
                "A strict integer partition is represented by a finite set of positive "
                    + "parts. A family assigns one block to every member of S, with that "
                    + "member as its sum. Blocks for different members must be disjoint. "
                    + "NontrivialDisjointRefinement means at least one block differs from "
                    + "the singleton of its member; values of the block function outside S "
                    + "do not enter this predicate.")),
            Describe.Lean(
                DescribeId.Create("nontrivial-disjoint-refinement-iff-outside-sum"),
                DeclarationHandle.Create(
                    "D5/S3/ArithSums/DisjointStrictRefinement."
                        + "nontrivial_disjoint_refinement_iff"),
                H("A changed family exists exactly when an outside sum exists"),
                StatementSource.FromAuthor(Criterion()),
                AssessedProvenance.FromRepo(Oeis),
                Blocks(
                    Paragraph(Text(
                        "Choose the smallest member whose block has changed. Each part of "
                            + "this block is strictly smaller than its sum: equality would "
                            + "force every other positive summand to disappear. If a part "
                            + "were in S, minimality would leave its own singleton block "
                            + "unchanged, contradicting pairwise disjointness.")),
                    Paragraph(Text(
                        "Conversely, replace the selected singleton by its partition into "
                            + "positive nonmembers and keep every other singleton. The new "
                            + "family is disjoint and the selected block has changed. The "
                            + "empty set is included: it cannot supply a changed member.")),
                    Paragraph(Text(
                        "The same pointwise criterion applies when S ranges over subsets "
                            + "of an initial interval (A384350) or over strict partitions "
                            + "of a total (A384318). The cited entries state the question; "
                            + "the proof here is a repository derivation. No sequence "
                            + "coefficient computation is part of this theorem."))),
                DescribeRole.Theorem))));

    private static Formula Criterion()
    {
        Formula s = F.Id("s");
        Formula set = F.Id("S");
        Formula parts = F.Id("T");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteSets = Call("Finset", naturals);
        Formula sum = Call("sum", parts, F.Id("id"));
        Formula outside = And(Positive(parts), And(Call("Disjoint", parts, set),
            new Formula.Relation(sum, FormulaRelationOperator.Equal, s)));
        Formula existsParts = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("T"), finiteSets, outside);
        Formula existsMember = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("s"), naturals, And(Member(s, set), existsParts));
        Formula criterion = new Formula.Logic(Call("NontrivialDisjointRefinement", set),
            FormulaLogicOperator.Iff, existsMember);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("S"), finiteSets,
            new Formula.Logic(Positive(set), FormulaLogicOperator.Implies, criterion)));
    }

    private static Formula Positive(Formula set)
    {
        Formula t = F.Id("t");
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("t"),
            Seq(Mathbb, Grp(F.Id("N"))), new Formula.Logic(Member(t, set),
                FormulaLogicOperator.Implies,
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, t)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Member(Formula x, Formula set) =>
        new Formula.Relation(x, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
