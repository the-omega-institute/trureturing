using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class CyclicStackPreimagesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/Patterns/CyclicStackPreimages.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/zhanbie2026cyclicstack");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The consecutive cyclic [123] stack has the exact even and odd fibres conjectured by Zhan and Bie.",
        H("Exact Consecutive Cyclic-Stack Fibres"),
        Blocks(
            Paragraph(Text(
                "The stack is top-first. For each incoming value, it repeatedly pops the top "
                    + "entry exactly when the incoming value and the top two stack entries form "
                    + "one of the consecutive patterns 123, 231, or 312, then pushes the incoming "
                    + "value. The residual stack is flushed top-first. This literal convention "
                    + "maps 3124 to 4213, as in Figure 3 of the source.")),
            Describe.Lean(
                DescribeId.Create("zhan-bie-conjectures-3-4"),
                DeclarationHandle.Create(Prefix + "zhan_bie_conjectures_3_4"),
                H("The full even and odd fibres"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For m at least two, fibre(n) is the complete list of permutations of "
                        + "1 through n whose output is (1,...,floor(n/2),n,...,floor(n/2)+1). "
                        + "The two conjuncts therefore cover every n at least four: the even "
                        + "fibre has one element, and the odd fibre has m+1 elements, equal to "
                        + "ceiling(n/2). The proof classifies every successful input rather than "
                        + "only constructing the displayed number of witnesses."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var m = F.Id("m");
        var even = Multiply(D(2), m);
        var odd = Add(even, D(1));
        var hypothesis = LessThanOrEqual(D(2), m);
        var evenCount = Equal(Length(Call("fibre", even)), D(1));
        var oddCount = Equal(Length(Call("fibre", odd)), Add(m, D(1)));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("m"),
            Naturals(),
            Implies(hypothesis, And(evenCount, oddCount))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Length(Formula value) => Call("length", value);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
