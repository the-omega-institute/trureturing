using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class EscapePairsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/EscapePairs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite indistinguishable pairs split into persistent and theorem-unique escape.",
        H("Finite Escape Pairs"),
        Blocks(
            Definition("escape-pairs", "escapePairs", H("Selected escape pairs"), EscapePairs()),
            Definition("unique-capture-pairs", "uniqueCapturePairs",
                H("Unique capture pairs"), UniqueCapturePairs()),
            Theorem("unique-capture-pairs-eq-sdiff", "uniqueCapturePairs_eq_sdiff",
                H("Unique capture is finite difference"), UniqueDifference()),
            Theorem("escape-pairs-anti", "escapePairs_anti",
                H("Escape pairs are antitone"), Antitone()),
            Theorem("escape-pairs-insert", "escapePairs_insert",
                H("Insertion filters escape pairs"), Insert()),
            Theorem("escape-pairs-full-subset-without", "escapePairs_full_subset_without",
                H("Full escape lies in leave-one-out escape"), FullSubset()),
            Theorem("escape-pairs-without-eq-union", "escapePairs_without_eq_union",
                H("Leave-one-out escape decomposes"), Decomposition()),
            Theorem("escape-pairs-full-disjoint-unique-capture-pairs",
                "escapePairs_full_disjoint_uniqueCapturePairs",
                H("Persistent and unique escape are disjoint"), Disjointness()))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, Heading title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), title,
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "This executable finite-set definition uses the catalog's decidable kernels."))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, Heading title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), title,
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The proof reuses the canonical finite catalog kernel and Mathlib Finset laws."))),
            DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Escape(Formula selected) =>
        Call("escapePairs", F.Id("C"), selected);

    private static Formula Unique() =>
        Call("uniqueCapturePairs", F.Id("C"), F.Id("i"));

    private static Formula Without() => Call("without", F.Id("C"), F.Id("i"));

    private static Formula Full() => Call("fullIndexSet", F.Id("C"));

    private static Formula EscapePairs() => Seq(
        Escape(F.Id("S")), Sp, Eq, Sp,
        Call("filter", Call("offDiagonalPairs", F.Id("X")),
            Seq(LambdaLower, Sp, F.Id("p"), Comma, Sp,
                Call("indistinguishable", F.Id("C"), F.Id("S"),
                    F.Id("p1"), F.Id("p2")))));

    private static Formula UniqueCapturePairs() => Seq(
        Unique(), Sp, Eq, Sp,
        Call("filter", Escape(Without()),
            Seq(LambdaLower, Sp, F.Id("p"), Comma, Sp, Neg,
                Call("agrees", Call("theoremAt", F.Id("C"), F.Id("i")),
                    F.Id("p1"), F.Id("p2")))));

    private static Formula UniqueDifference() => Seq(
        Unique(), Sp, Eq, Sp, Escape(Without()), Sp, Setminus, Sp, Escape(Full()));

    private static Formula Antitone() => new Formula.Logic(
        Seq(F.Id("S"), Sp, Subseteq, Sp, F.Id("T")),
        FormulaLogicOperator.Implies,
        Seq(Escape(F.Id("T")), Sp, Subseteq, Sp, Escape(F.Id("S"))));

    private static Formula Insert() => Seq(
        Escape(Call("insert", F.Id("i"), F.Id("S"))), Sp, Eq, Sp,
        Call("filter", Escape(F.Id("S")),
            Seq(LambdaLower, Sp, F.Id("p"), Comma, Sp,
                Call("agrees", Call("theoremAt", F.Id("C"), F.Id("i")),
                    F.Id("p1"), F.Id("p2")))));

    private static Formula FullSubset() => Seq(
        Escape(Full()), Sp, Subseteq, Sp, Escape(Without()));

    private static Formula Decomposition() => Seq(
        Escape(Without()), Sp, Eq, Sp, Call("union", Escape(Full()), Unique()));

    private static Formula Disjointness() =>
        Call("Disjoint", Escape(Full()), Unique());
}
