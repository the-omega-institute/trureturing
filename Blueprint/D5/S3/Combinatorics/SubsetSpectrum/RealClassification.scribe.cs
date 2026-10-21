using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class RealClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/RealClassification.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/bhargava2026facemagic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd-length real even-subset spectra classify coefficients up to even zero-sum sign permutations.",
        H("Classification of real even-subset spectra"),
        Blocks(
            Describe.Lean(DescribeId.Create("real-even-classification"),
                DeclarationHandle.Create(Prefix + "real_even_spectrum_classification"),
                H("The full odd-length classification"), StatementSource.FromAuthor(Classification()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every odd m at least three and arbitrary real families "
                    + "b,c on Fin m, the even occurrence spectra are equal if and only if there exist "
                    + "a permutation sigma of Fin m and an index set I with even cardinality and "
                    + "sum_I b=0 such that c(sigma i)=-b(i) on I and c(sigma i)=b(i) off I. "
                    + "All zero and repeated coefficients remain in scope. The first moment and "
                    + "complement reflection recover the full spectra; their minima determine "
                    + "the signed normalization. Nonnegative recovery then matches absolute-value "
                    + "occurrences by a permutation. Equality of totals forces the flip sum to vanish. "
                    + "If its parity is odd, a zero coefficient permits a parity repair; without "
                    + "a zero coefficient, the unique minimizing subset prevents odd parity. "
                    + "Conversely, symmetric difference with an even zero-sum index set preserves "
                    + "all even subset sums and their multiplicities."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SubsetSpectrum/SignAction"))]));

    private static Formula Classification()
    {
        var m = F.Id("m"); var b = F.Id("b"); var c = F.Id("c");
        var sigma = F.Id("sigma"); var set = F.Id("I"); var i = F.Id("i");
        var fin = Call("Fin", m);
        var values = new Formula.TypeArrow(fin, new Formula.NamedConstant(FormulaIdentifier.Create("Real")));
        var member = Rel(i, FormulaRelationOperator.MemberOf, set);
        var signs = All("i", fin, And(
            Imp(member, Equal(Call("c", Call("sigma", i)), new Formula.Negate(Call("b", i)))),
            Imp(new Formula.Not(member), Equal(Call("c", Call("sigma", i)), Call("b", i)))));
        var witness = ExistsIn("sigma", Call("Perm", fin), ExistsIn("I", Call("Finset", fin),
            And(Call("Even", Call("card", set)), Equal(Call("sum", set, b), D(0)), signs)));
        return Disp(All("m", new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), Imp(
            And(Rel(D(3), FormulaRelationOperator.LessThanOrEqual, m), Call("Odd", m)),
            All("b", values, All("c", values, new Formula.Logic(
                Equal(Call("E", b), Call("E", c)), FormulaLogicOperator.Iff, witness))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsIn(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(params Formula[] parts)
    {
        Formula result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
}
