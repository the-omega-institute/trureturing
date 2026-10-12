using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AssociatedMersenne;

internal sealed class MarkedDegreeEnumerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/wei2024associatedmersenne");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Degree enumeration for labelled circular run-constrained words.", H("MarkedDegreeEnumeration"), Blocks(
        Node("DegreeTuples", "DegreeTuples", Disp(All(Name("n"), Name("Nat"), All(Name("ell"), Name("Nat"), All(Name("k"), Name("Nat"), Seq(Name("DegreeTuples"), Sp, Name("n"), Sp, Name("ell"), Sp, Name("k"), Sp, Eq, Sp, Parenthesized(Seq(OpenBrace, Sp, Seq(Name("t"), Sp, Colon, Sp, Name("GoodTuple"), Sp, Name("n"), Sp, Seq(Slash,Slash), Sp, Name("t.val.length"), Sp, Eq, Sp, Name("ell"), Sp, Land, Sp, Name("tupleDegree"), Sp, Name("t.val"), Sp, Eq, Sp, Name("k")), Sp, CloseBrace))))))), "The subtype fixes the number of tuple pairs and their exact tuple degree.", DescribeRole.Definition),
        Node("instFintypeDegreeTuples", "instFintypeDegreeTuples", Disp(All(Name("n"), Name("Nat"), All(Name("ell"), Name("Nat"), All(Name("k"), Name("Nat"), Seq(Name("instFintypeDegreeTuples"), Sp, Name("n"), Sp, Name("ell"), Sp, Name("k"), Sp, Colon, Sp, Name("Fintype"), Sp, Parenthesized(Seq(Name("DegreeTuples"), Sp, Name("n"), Sp, Name("ell"), Sp, Name("k")))))))), "This instance is inferInstanceAs for the subtype of RunTuples n ell whose tupleDegree equals k.", DescribeRole.Definition),
        Node("marked_degree_double_count", "marked degree double count", Disp(All(Name("n"), Name("Nat"), All(Name("ell"), Name("Nat"), All(Name("k"), Name("Nat"), Seq(Name("ell"), Sp, Cdot, Sp, Name("Fintype.card"), Sp, Parenthesized(Seq(Name("DegreeRunWords"), Sp, Name("n"), Sp, Name("ell"), Sp, Name("k"))), Sp, Eq, Sp, Name("n"), Sp, Cdot, Sp, Name("Fintype.card"), Sp, Parenthesized(Seq(Name("DegreeTuples"), Sp, Name("n"), Sp, Name("ell"), Sp, Name("k")))))))), "The marked word-to-tuple equivalence preserves degree and converts run marks into labelled origins.", DescribeRole.Theorem),
        Node("degreePolynomial", "degreePolynomial", Disp(All(Name("n"), Name("Nat"), Seq(Name("degreePolynomial"), Sp, Name("n"), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, Name("k"), Sp, InMacro, Sp, Name("Finset.range"), Sp, Parenthesized(Seq(Name("n"), Sp, Plus, Sp, D(1))), Sp, Comma, Sp, Name("Polynomial.C"), Sp, Parenthesized(Seq(Name("N"), Sp, Name("n"), Sp, Name("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, new Formula.Power(Name("Polynomial.X"), Name("k"))))))), "Summing the histogram with monomials in the degree records all labelled admissible words.", DescribeRole.Definition),
        Node("instFintypeRunTuples", "instFintypeRunTuples", Disp(All(Name("n"), Name("Nat"), All(Name("ell"), Name("Nat"), Seq(Name("instFintypeRunTuples"), Sp, Name("n"), Sp, Name("ell"), Sp, Colon, Sp, Name("Fintype"), Sp, Parenthesized(Seq(Name("RunTuples"), Sp, Name("n"), Sp, Name("ell"))))))), "This instance is inferInstanceAs for the subtype of GoodTuple n whose underlying list has length ell.", DescribeRole.Definition),
        Node("runCount_le", "runCount le", Disp(All(Name("n"), Name("Nat"), All(Name("w"), Seq(Name("Fin"), Sp, Name("n"), Sp, To, Sp, Name("Bool")), Seq(Name("runCount"), Sp, Name("w"), Sp, Le, Sp, Name("n"))))), "Marked starts form a subset of the labelled positions, bounding the number of runs by the length.", DescribeRole.Lemma),
        Node("runPolynomial", "runPolynomial", Disp(All(Name("n"), Name("Nat"), All(Name("ell"), Name("Nat"), Seq(Name("runPolynomial"), Sp, Name("n"), Sp, Name("ell"), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, Name("k"), Sp, InMacro, Sp, Name("Finset.range"), Sp, Parenthesized(Seq(Name("n"), Sp, Plus, Sp, D(1))), Sp, Comma, Sp, Name("Polynomial.C"), Sp, Parenthesized(Seq(Parenthesized(Seq(Name("Fintype.card"), Sp, Parenthesized(Seq(Name("DegreeRunWords"), Sp, Name("n"), Sp, Name("ell"), Sp, Name("k"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Seq(Name("Polynomial.X"), Sp, Colon, Sp, Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Name("k")))))))), "Filtering additionally by the number of circular runs gives the degree-refined run polynomial.", DescribeRole.Definition),
        Node("tuplePolynomial", "tuplePolynomial", Disp(All(Name("n"), Name("Nat"), All(Name("ell"), Name("Nat"), Seq(Name("tuplePolynomial"), Sp, Name("n"), Sp, Name("ell"), Sp, Eq, Sp, Parenthesized(Seq(Sum, Sp, Name("k"), Sp, InMacro, Sp, Name("Finset.range"), Sp, Parenthesized(Seq(Name("n"), Sp, Plus, Sp, D(1))), Sp, Comma, Sp, Name("Polynomial.C"), Sp, Parenthesized(Seq(Parenthesized(Seq(Name("Fintype.card"), Sp, Parenthesized(Seq(Name("DegreeTuples"), Sp, Name("n"), Sp, Name("ell"), Sp, Name("k"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Seq(Name("Polynomial.X"), Sp, Colon, Sp, Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Name("k")))))))), "Counting positive tuples by their tuple degree gives the corresponding run-refined weight polynomial.", DescribeRole.Definition),
        Node("polynomial_marked_double_count", "polynomial marked double count", Disp(All(Name("n"), Name("Nat"), All(Name("ell"), Name("Nat"), Seq(Parenthesized(Seq(Name("ell"), Sp, Colon, Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Name("runPolynomial"), Sp, Name("n"), Sp, Name("ell"), Sp, Eq, Sp, Parenthesized(Seq(Name("n"), Sp, Colon, Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Name("tuplePolynomial"), Sp, Name("n"), Sp, Name("ell"))))), "Applying the marked count to each degree coefficient gives the integer polynomial double-count identity.", DescribeRole.Theorem),
        Node("tuplePolynomial_eq_sum", "tuplePolynomial eq sum", Disp(All(Name("n"), Name("Nat"), All(Name("ell"), Name("Nat"), Seq(Name("tuplePolynomial"), Sp, Name("n"), Sp, Name("ell"), Sp, Eq, Sp, Sum, Sp, Name("t"), Sp, Colon, Sp, Name("RunTuples"), Sp, Name("n"), Sp, Name("ell"), Sp, Comma, Sp, new Formula.Power(Parenthesized(Seq(Name("Polynomial.X"), Sp, Colon, Sp, Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Seq(Name("tupleDegree"), Sp, Name("t.val.val"))))))), "Partitioning the finite tuple set by degree turns the histogram polynomial into a sum of tuple weights.", DescribeRole.Theorem),
        Node("degreePolynomial_partition", "degreePolynomial partition", Disp(All(Name("n"), Name("Nat"), Seq(Name("degreePolynomial"), Sp, Name("n"), Sp, Eq, Sp, Sum, Sp, Name("ell"), Sp, InMacro, Sp, Name("Finset.range"), Sp, Parenthesized(Seq(Name("n"), Sp, Plus, Sp, D(1))), Sp, Comma, Sp, Name("runPolynomial"), Sp, Name("n"), Sp, Name("ell")))), "Partitioning admissible words by their run count recovers the full degree polynomial.", DescribeRole.Lemma),
        Node("runPolynomial_zero", "runPolynomial zero", Disp(All(Name("n"), Name("Nat"), Seq(Name("runPolynomial"), Sp, Name("n"), Sp, D(0), Sp, Eq, Sp, new Formula.Power(Parenthesized(Seq(Name("Polynomial.X"), Sp, Colon, Sp, Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Parenthesized(Seq(Name("if"), Sp, Name("n"), Sp, Le, Sp, D(2), Sp, Name("then"), Sp, D(0), Sp, Name("else"), Sp, Name("n"))))))), "A zero-run admissible word is the zero word, whose degree fixes its single polynomial weight.", DescribeRole.Lemma),
        Describe.Lean(DescribeId.Create("amg-markeddegreeenumeration-runcount-zero-iff"), DeclarationHandle.Create(Prefix + "runCount_zero_iff"), H("Zero run count"), StatementSource.FromAuthor(Disp(All(Name("n"), Seq(Name("Nat")), All(Name("w"), Seq(Name("Fin"), Sp, Name("n"), Sp, To, Sp, Name("Bool")), All(Name("ha"), Seq(Name("Admissible"), Sp, Name("w")), Seq(Name("runCount"), Sp, Name("w"), Sp, Eq, Sp, D(0), Sp, Iff, Sp, Name("w"), Sp, Eq, Sp, Seq(Open, Name("Function.const"), Sp, Seq(Open, Name("Fin"), Sp, Name("n"), Close), Sp, Name("false"), Close))))))), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("For an admissible word, zero run count is equivalent to being the all-false word."))), DescribeRole.Lemma)
)));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, bool literature = false) => Describe.Lean(
        DescribeId.Create("amg-markeddegreeenumeration-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Name(string name) {
        var parts = name.Split('.');
        Formula value = Word(parts[0]);
        for (var i = 1; i < parts.Length; i++) value = Seq(value, Dot, Word(parts[i]));
        return value;
    }
    private static Formula Word(string word) {
        if (word == "") return Sp;
        if (word == "0") return D(0);
        if (word == "1") return D(1);
        if (word == "2") return D(2);
        if (word.EndsWith("'", StringComparison.Ordinal)) return Seq(Word(word[..^1]), Apos);
        var parts = word.Split('_');
        Formula value = Seq(Operatorname, Grp(F.Id(parts[0])));
        for (var i = 1; i < parts.Length; i++) value = new Formula.Subscript(value, Seq(Operatorname, Grp(F.Id(parts[i]))));
        return value;
    }
}
