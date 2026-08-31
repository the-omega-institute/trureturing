using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class SourceContributionDecompositionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source contributions have unique ordered decompositions exactly when disjoint.",
        H("Source Contribution Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-contribution-unique-decomposition"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Linear/SourceContributionDecomposition."
                    + "source_contribution_unique_decomposition_iff_disjoint"),
            H("Unique source decomposition is equivalent to disjointness"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the observer and external sources be submodules of the same module. "
                        + "Every element of their sum has an ordered decomposition into one "
                        + "observer contribution and one external contribution.")),
                Paragraph(Text(
                    "Such decompositions are unique exactly when the two source submodules "
                        + "are disjoint. Equivalently, the addition map from their product "
                        + "into the ambient module is injective."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("R");
        Formula space = F.Id("Y");
        Formula observer = new Formula.Subscript(F.Id("S"), F.Id("O"));
        Formula external = new Formula.Subscript(F.Id("S"), F.Id("E"));
        Formula vector = F.Id("y");
        Formula decomposition = F.Id("d");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula submodule = Call("Submodule", scalar, space);
        Formula sourceProduct = Seq(observer, Sp, Times, Sp, external);
        Formula sourceSum = Call("sup", observer, external);
        Formula observerPart = new Formula.Subscript(decomposition, D(1));
        Formula externalPart = new Formula.Subscript(decomposition, D(2));
        Formula uniqueDecomposition = Seq(
            Forall, Sp, Typed(vector, space), Comma, Sp,
            vector, Sp, InMacro, Sp, sourceSum, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, Typed(decomposition, sourceProduct), Comma, Sp,
            observerPart, Sp, Plus, Sp, externalPart, Sp, Eq, Sp, vector);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(Seq(scalar, Comma, Sp, space), type), Comma),
            Seq(
                Grp(), Typeclass("Ring", scalar), Comma, Sp,
                Typeclass("AddCommGroup", space), Comma, Sp,
                Typeclass("Module", scalar, space), Comma),
            Seq(
                Forall, Sp,
                Typed(Seq(observer, Comma, Sp, external), submodule), Comma),
            Seq(
                Open, uniqueDecomposition, Close, Sp, Iff, Sp,
                Call("Disjoint", observer, external), Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

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
}
